#!/usr/bin/env python3
"""
WIT Sales Tracker — secure web backend
======================================
One Flask app that makes the tracker a real, secured web application:

  * Serves the tracker SPA (wit-sales-tracker.html).
  * Authenticates users with Google — the ID token is VERIFIED server-side
    (signature, audience, expiry, domain), not trusted from the browser.
  * Issues a signed, HttpOnly, Secure session cookie (stateless; works across
    gunicorn workers as long as WIT_SECRET_KEY is stable).
  * Stores ALL agency data server-side in SQLite. Every data call requires a
    valid session — nothing sensitive lives in the browser anymore.
  * Sends the sale-notification email (SMTP / SendGrid / console).

This supersedes wit_sale_hook.py (the email logic is folded in at /api/notify).
It runs alongside WIT-FM on the same box: its own port + systemd unit.

Install:
    pip install flask google-auth gunicorn

Run (dev):
    export WIT_GOOGLE_CLIENT_ID=xxxx.apps.googleusercontent.com
    export WIT_ALLOWED_DOMAINS=weinsurethings.com
    export WIT_SECRET_KEY=$(python3 -c "import secrets;print(secrets.token_hex(32))")
    export WIT_COOKIE_SECURE=false        # true once you're on https
    python3 wit_app.py

Run (prod):
    gunicorn -w 2 -b 127.0.0.1:8093 wit_app:app

The client auto-detects this backend (via /api/config) and switches from
local storage to the secure API automatically — no edit needed in the HTML.
"""
import os
import json
import sqlite3
import smtplib
import logging
import secrets
import urllib.request
import urllib.parse
from datetime import datetime, timezone, timedelta
from functools import wraps
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import formataddr

from flask import Flask, request, jsonify, session, send_file, g

from google.oauth2 import id_token as google_id_token
from google.auth.transport import requests as google_requests

# --------------------------------------------------------------------------- #
# Config
# --------------------------------------------------------------------------- #
CLIENT_ID       = os.environ.get("WIT_GOOGLE_CLIENT_ID", "")
ALLOWED_DOMAINS = [d.strip().lower() for d in os.environ.get("WIT_ALLOWED_DOMAINS", "weinsurethings.com").split(",") if d.strip()]
ALLOWED_EMAILS  = [e.strip().lower() for e in os.environ.get("WIT_ALLOWED_EMAILS", "").split(",") if e.strip()]
SECRET_KEY      = os.environ.get("WIT_SECRET_KEY")
DB_PATH         = os.environ.get("WIT_DB_PATH", "wit_tracker.db")
INDEX_PATH      = os.environ.get("WIT_INDEX_PATH", "wit-sales-tracker.html")

# email
EMAIL_BACKEND = os.environ.get("WIT_EMAIL_BACKEND", "console").lower()   # smtp | sendgrid | console
FROM_EMAIL    = os.environ.get("WIT_FROM_EMAIL", "wit-tracker@weinsurethings.com")
FROM_NAME     = os.environ.get("WIT_FROM_NAME", "WIT Sales Tracker")
SMTP_HOST     = os.environ.get("WIT_SMTP_HOST", "smtp.gmail.com")
SMTP_PORT     = int(os.environ.get("WIT_SMTP_PORT", "587"))
SMTP_USER     = os.environ.get("WIT_SMTP_USER", "")
SMTP_PASS     = os.environ.get("WIT_SMTP_PASS", "")
SMTP_TLS      = os.environ.get("WIT_SMTP_TLS", "true").lower() == "true"
SENDGRID_KEY  = os.environ.get("WIT_SENDGRID_KEY", "")

# roles
ADMIN_EMAILS = [e.strip().lower() for e in os.environ.get("WIT_ADMINS", "").split(",") if e.strip()]

# NowCerts AMS integration
NC_BASE     = os.environ.get("WIT_NOWCERTS_BASE", "https://api.nowcerts.com")
NC_USERNAME = os.environ.get("WIT_NOWCERTS_USERNAME", "")
NC_PASSWORD = os.environ.get("WIT_NOWCERTS_PASSWORD", "")
NC_ENABLED  = bool(NC_USERNAME and NC_PASSWORD)
_nc_token   = {"value": None, "exp": 0}

# Map our line names -> NowCerts line-of-business names. Override with
# WIT_NOWCERTS_LOB_MAP (JSON). Anything unmapped is sent through as-is.
NC_LOB_DEFAULT = {
    "Auto": "Personal Auto", "Home": "Homeowners", "Bundle (Auto+Home)": "Personal Auto",
    "Renters": "Renters/Tenants", "Commercial": "Commercial Package",
    "General Liability": "General Liability", "Workers Comp": "Workers Compensation",
    "Life": "Life", "Health": "Health", "Umbrella": "Umbrella", "Other": "Other",
}
try:
    NC_LOB_MAP = {**NC_LOB_DEFAULT, **json.loads(os.environ.get("WIT_NOWCERTS_LOB_MAP", "{}"))}
except (ValueError, TypeError):
    NC_LOB_MAP = dict(NC_LOB_DEFAULT)

# --------------------------------------------------------------------------- #
# We Insure Things brand colors — kept in sync with :root in wit-sales-tracker.html
# --------------------------------------------------------------------------- #
BRAND_BLUE        = "#00aeef"   # --amber  (WIT sky blue — primary accent)
BRAND_DARK        = "#06121d"   # --navy / --ink  (dark navy — headers, body text)
BRAND_WHITE       = "#ffffff"   # --surface
BRAND_LIGHT_BG    = "#e8f1f8"   # --bg
BRAND_TEXT        = "#36485a"   # --ink-soft  (secondary body copy)
BRAND_MUTED       = "#6b7280"   # --muted
BRAND_BORDER      = "#dbe7f1"   # --line
BRAND_SUCCESS     = "#15a05c"   # --emerald

logging.basicConfig(level=logging.INFO, format="%(asctime)s  %(levelname)s  %(message)s")
log = logging.getLogger("wit_app")

if not SECRET_KEY:
    SECRET_KEY = secrets.token_hex(32)
    log.warning("WIT_SECRET_KEY not set — using a random key. Sessions will reset on restart. Set it in prod!")

app = Flask(__name__)
app.config.update(
    SECRET_KEY=SECRET_KEY,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SECURE=os.environ.get("WIT_COOKIE_SECURE", "true").lower() == "true",
    SESSION_COOKIE_SAMESITE="Lax",
    PERMANENT_SESSION_LIFETIME=60 * 60 * 12,   # 12h
    MAX_CONTENT_LENGTH=6 * 1024 * 1024,        # 6 MB cap on request bodies
)

# --------------------------------------------------------------------------- #
# Database (simple authenticated key/value store of the agency's data)
# --------------------------------------------------------------------------- #
def db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
        cur = g.db
        cur.execute("CREATE TABLE IF NOT EXISTS kv (key TEXT PRIMARY KEY, value TEXT NOT NULL, updated TEXT)")
        cur.execute("""CREATE TABLE IF NOT EXISTS sales (
            id TEXT PRIMARY KEY, date TEXT, producer TEXT, customer TEXT, line TEXT, carrier TEXT,
            type TEXT, status TEXT, premium REAL, rate TEXT, notes TEXT, commission REAL,
            created_by TEXT, created_by_name TEXT, created_at TEXT, updated_at TEXT)""")
        cur.execute("""CREATE TABLE IF NOT EXISTS todos (
            id TEXT PRIMARY KEY, text TEXT, due TEXT, prio TEXT, done INTEGER,
            created_by TEXT, created_at TEXT, completed_at TEXT)""")
        cur.execute("CREATE TABLE IF NOT EXISTS settings (id TEXT PRIMARY KEY, value TEXT)")
        cur.execute("""CREATE TABLE IF NOT EXISTS hotlist (
            id TEXT PRIMARY KEY, name TEXT, action TEXT, due TEXT, emoji TEXT,
            created_by TEXT, created_at TEXT)""")
        cur.execute("CREATE TABLE IF NOT EXISTS audit (\n            id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, actor TEXT,\n            action TEXT, entity TEXT, entity_id TEXT, detail TEXT)")
        cur.execute("CREATE TABLE IF NOT EXISTS prefs (email TEXT PRIMARY KEY, value TEXT)")
        # NowCerts sync columns (added to existing DBs too)
        for col in ("nc_insured_id TEXT", "nc_policy_id TEXT", "nc_pushed_at TEXT"):
            try:
                cur.execute(f"ALTER TABLE sales ADD COLUMN {col}")
            except sqlite3.OperationalError:
                pass
        g.db.commit()
    return g.db


def now_iso():
    return datetime.now(timezone.utc).isoformat()


def audit(action, entity, entity_id, detail=""):
    u = current_user() or {}
    db().execute("INSERT INTO audit(ts,actor,action,entity,entity_id,detail) VALUES(?,?,?,?,?,?)",
                 (now_iso(), u.get("email", "?"), action, entity, str(entity_id), detail))


SALE_FIELDS = ["date", "producer", "customer", "line", "carrier", "type", "status", "premium", "rate", "notes"]


def sale_to_dict(r):
    return {k: r[k] for k in r.keys()}


@app.teardown_appcontext
def _close_db(_):
    d = g.pop("db", None)
    if d:
        d.close()


# --------------------------------------------------------------------------- #
# Auth
# --------------------------------------------------------------------------- #
def current_user():
    return session.get("user")


def is_admin():
    u = current_user() or {}
    return u.get("role") == "admin"


def user_allowed(email):
    email = (email or "").lower()
    if email in ALLOWED_EMAILS:
        return True
    domain = email.split("@")[-1]
    return (not ALLOWED_DOMAINS) or domain in ALLOWED_DOMAINS


def login_required(f):
    @wraps(f)
    def wrapper(*a, **k):
        if not current_user():
            return jsonify(error="authentication required"), 401
        return f(*a, **k)
    return wrapper


@app.get("/api/config")
def config():
    # Public: lets the SPA know the backend is live and which client ID to use.
    return jsonify(clientId=CLIENT_ID, allowedDomains=ALLOWED_DOMAINS)


@app.post("/api/auth/google")
def auth_google():
    if not CLIENT_ID:
        return jsonify(error="server not configured (WIT_GOOGLE_CLIENT_ID)"), 500
    cred = (request.get_json(silent=True) or {}).get("credential", "")
    try:
        info = google_id_token.verify_oauth2_token(cred, google_requests.Request(), CLIENT_ID)
    except Exception as exc:                       # noqa: BLE001
        log.warning("token verification failed: %s", exc)
        return jsonify(error="invalid token"), 401

    email = info.get("email", "")
    if not info.get("email_verified"):
        return jsonify(error="email not verified"), 403
    if not user_allowed(email):
        log.info("blocked sign-in: %s", email)
        return jsonify(error="account not authorized"), 403

    user = {"email": email, "name": info.get("name"), "picture": info.get("picture"),
            "role": "admin" if email.lower() in ADMIN_EMAILS else "producer"}
    session.permanent = True
    session["user"] = user
    log.info("sign-in: %s", email)
    return jsonify(user=user)


@app.get("/api/me")
def me():
    u = current_user()
    return (jsonify(user=u), 200) if u else (jsonify(user=None), 401)


@app.post("/api/logout")
def logout():
    session.clear()
    return jsonify(ok=True)


# --------------------------------------------------------------------------- #
# Data API (authenticated key/value — the client stores sales/todos/settings here)
# --------------------------------------------------------------------------- #
@app.get("/api/kv/<key>")
@login_required
def kv_get(key):
    row = db().execute("SELECT value FROM kv WHERE key=?", (key,)).fetchone()
    if not row:
        return jsonify(value=None), 404
    return jsonify(value=json.loads(row["value"]))


@app.put("/api/kv/<key>")
@login_required
def kv_put(key):
    body = request.get_json(silent=True) or {}
    value = json.dumps(body.get("value"))
    db().execute(
        "INSERT INTO kv(key, value, updated) VALUES(?,?,?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated=excluded.updated",
        (key, value, datetime.now(timezone.utc).isoformat()),
    )
    db().commit()
    return jsonify(ok=True)


# ---- Sales (per-record, stamped with the signed-in producer) ----
def _calc_commission(premium, rate):
    try:
        if rate not in (None, ""):
            return round(float(premium or 0) * float(rate) / 100.0, 2)
    except (TypeError, ValueError):
        pass
    return None


@app.get("/api/sales")
@login_required
def sales_list():
    rows = db().execute("SELECT * FROM sales ORDER BY date DESC, created_at DESC").fetchall()
    return jsonify(sales=[sale_to_dict(r) for r in rows])


@app.post("/api/sales")
@login_required
def sales_create():
    u = current_user()
    b = request.get_json(silent=True) or {}
    rec = {k: b.get(k) for k in SALE_FIELDS}
    rec["id"] = b.get("id") or secrets.token_hex(8)
    rec["producer"] = rec.get("producer") or u.get("name") or u.get("email")   # auto-stamp producer
    rec["commission"] = _calc_commission(rec.get("premium"), rec.get("rate"))
    rec["created_by"] = u.get("email")
    rec["created_by_name"] = u.get("name")
    rec["created_at"] = rec["updated_at"] = now_iso()
    cols = ",".join(rec.keys())
    db().execute(f"INSERT INTO sales({cols}) VALUES({','.join('?' for _ in rec)})", list(rec.values()))
    audit("create", "sale", rec["id"], f'{rec.get("customer")} · {rec.get("premium")}')
    db().commit()
    nc = _maybe_autopush(rec)
    return jsonify(sale=rec, nowcerts=nc), 201


def _maybe_autopush(rec):
    """If auto-push is on and the sale is bound, push to NowCerts. Never fails the save."""
    if not NC_ENABLED or rec.get("status") != "Bound" or rec.get("nc_pushed_at"):
        return None
    st = agency_settings()
    if not st.get("nowcertsAutoPush"):
        return None
    try:
        iid, pid, _ = nc_push_sale(rec, st)
        db().execute("UPDATE sales SET nc_insured_id=?, nc_policy_id=?, nc_pushed_at=? WHERE id=?",
                     (iid, pid, now_iso(), rec["id"]))
        audit("auto-push-nowcerts", "sale", rec["id"], f"insured {iid}")
        db().commit()
        rec["nc_pushed_at"] = now_iso()
        return "ok"
    except Exception as exc:                       # noqa: BLE001
        log.warning("NowCerts auto-push failed for %s: %s", rec.get("id"), exc)
        return "failed"


@app.patch("/api/sales/<sid>")
@login_required
def sales_update(sid):
    owner = db().execute("SELECT created_by FROM sales WHERE id=?", (sid,)).fetchone()
    if not owner:
        return jsonify(error="not found"), 404
    if not is_admin() and owner["created_by"] != current_user()["email"]:
        return jsonify(error="you can only edit your own sales"), 403
    b = request.get_json(silent=True) or {}
    fields = {k: b[k] for k in SALE_FIELDS if k in b}
    if not fields:
        return jsonify(error="no fields"), 400
    fields["commission"] = _calc_commission(b.get("premium"), b.get("rate"))
    fields["updated_at"] = now_iso()
    sets = ",".join(f"{k}=?" for k in fields)
    db().execute(f"UPDATE sales SET {sets} WHERE id=?", list(fields.values()) + [sid])
    audit("update", "sale", sid)
    db().commit()
    row = db().execute("SELECT * FROM sales WHERE id=?", (sid,)).fetchone()
    return jsonify(sale=sale_to_dict(row))


@app.delete("/api/sales/<sid>")
@login_required
def sales_delete(sid):
    owner = db().execute("SELECT created_by FROM sales WHERE id=?", (sid,)).fetchone()
    if owner and not is_admin() and owner["created_by"] != current_user()["email"]:
        return jsonify(error="you can only delete your own sales"), 403
    db().execute("DELETE FROM sales WHERE id=?", (sid,))
    audit("delete", "sale", sid)
    db().commit()
    return ("", 204)


# ---- To-dos ----
@app.get("/api/todos")
@login_required
def todos_list():
    rows = db().execute("SELECT * FROM todos ORDER BY done, due").fetchall()
    return jsonify(todos=[{**dict(r), "done": bool(r["done"])} for r in rows])


@app.post("/api/todos")
@login_required
def todos_create():
    u = current_user()
    b = request.get_json(silent=True) or {}
    rec = {"id": b.get("id") or secrets.token_hex(8), "text": b.get("text", ""), "due": b.get("due", ""),
           "prio": b.get("prio", "med"), "created_by": u.get("email"), "created_at": now_iso()}
    db().execute("INSERT INTO todos(id,text,due,prio,done,created_by,created_at,completed_at) VALUES(?,?,?,?,0,?,?,NULL)",
                 (rec["id"], rec["text"], rec["due"], rec["prio"], rec["created_by"], rec["created_at"]))
    audit("create", "todo", rec["id"], rec["text"])
    db().commit()
    return jsonify(todo={**rec, "done": False, "completed_at": None}), 201


@app.patch("/api/todos/<tid>")
@login_required
def todos_update(tid):
    b = request.get_json(silent=True) or {}
    done = 1 if b.get("done") else 0
    db().execute("UPDATE todos SET done=?, completed_at=? WHERE id=?", (done, now_iso() if done else None, tid))
    audit("update", "todo", tid, "done" if done else "reopen")
    db().commit()
    return jsonify(ok=True)


@app.delete("/api/todos/<tid>")
@login_required
def todos_delete(tid):
    db().execute("DELETE FROM todos WHERE id=?", (tid,))
    db().commit()
    return ("", 204)


# ---- Settings (single shared document) ----
@app.get("/api/settings")
@login_required
def settings_get():
    row = db().execute("SELECT value FROM settings WHERE id='agency'").fetchone()
    return jsonify(value=json.loads(row["value"]) if row else {})


@app.put("/api/settings")
@login_required
def settings_put():
    val = json.dumps((request.get_json(silent=True) or {}).get("value", {}))
    db().execute("INSERT INTO settings(id,value) VALUES('agency',?) "
                 "ON CONFLICT(id) DO UPDATE SET value=excluded.value", (val,))
    audit("update", "settings", "agency")
    db().commit()
    return jsonify(ok=True)


# ---- Audit / activity feed ----
@app.get("/api/audit")
@login_required
def audit_list():
    limit = min(int(request.args.get("limit", 50)), 200)
    rows = db().execute("SELECT * FROM audit ORDER BY id DESC LIMIT ?", (limit,)).fetchall()
    return jsonify(events=[dict(r) for r in rows])


# ---- Hot List (each producer's own top prospects; max 20) ----
HOTLIST_MAX = 20


@app.get("/api/hotlist")
@login_required
def hot_list():
    me = current_user()["email"]
    rows = db().execute("SELECT * FROM hotlist WHERE created_by=? ORDER BY (due='' OR due IS NULL), due", (me,)).fetchall()
    return jsonify(hotlist=[dict(r) for r in rows], max=HOTLIST_MAX)


@app.post("/api/hotlist")
@login_required
def hot_create():
    me = current_user()["email"]
    count = db().execute("SELECT COUNT(*) AS c FROM hotlist WHERE created_by=?", (me,)).fetchone()["c"]
    if count >= HOTLIST_MAX:
        return jsonify(error=f"hot list is full ({HOTLIST_MAX} max)"), 409
    b = request.get_json(silent=True) or {}
    name = (b.get("name") or "").strip()
    if not name:
        return jsonify(error="name required"), 400
    rec = {"id": b.get("id") or secrets.token_hex(8), "name": name, "action": b.get("action", ""),
           "due": b.get("due", ""), "emoji": b.get("emoji", "🔥"), "created_by": me, "created_at": now_iso()}
    db().execute("INSERT INTO hotlist(id,name,action,due,emoji,created_by,created_at) VALUES(?,?,?,?,?,?,?)",
                 (rec["id"], rec["name"], rec["action"], rec["due"], rec["emoji"], me, rec["created_at"]))
    audit("create", "hotlist", rec["id"], name)
    db().commit()
    return jsonify(item=rec), 201


@app.patch("/api/hotlist/<hid>")
@login_required
def hot_update(hid):
    me = current_user()["email"]
    b = request.get_json(silent=True) or {}
    fields = {k: b[k] for k in ("name", "action", "due", "emoji") if k in b}
    if not fields:
        return jsonify(error="no fields"), 400
    sets = ",".join(f"{k}=?" for k in fields)
    cur = db().execute(f"UPDATE hotlist SET {sets} WHERE id=? AND created_by=?", list(fields.values()) + [hid, me])
    if not cur.rowcount:
        return jsonify(error="not found"), 404
    db().commit()
    row = db().execute("SELECT * FROM hotlist WHERE id=?", (hid,)).fetchone()
    return jsonify(item=dict(row))


@app.delete("/api/hotlist/<hid>")
@login_required
def hot_delete(hid):
    me = current_user()["email"]
    db().execute("DELETE FROM hotlist WHERE id=? AND created_by=?", (hid, me))
    audit("delete", "hotlist", hid)
    db().commit()
    return ("", 204)


# --------------------------------------------------------------------------- #
# Email on sale (folds in the old wit_sale_hook logic; now session-protected)
# --------------------------------------------------------------------------- #
def money(v):
    try:
        return "${:,.2f}".format(float(v or 0))
    except (TypeError, ValueError):
        return "$0.00"


def parse_recipients(raw):
    items = raw if isinstance(raw, list) else str(raw or "").replace(";", ",").split(",")
    return [e.strip() for e in items if e.strip()]


def build_html(sale, agency, fallback_text):
    rows = [
        ("Customer", sale.get("customer", "—")), ("Producer", sale.get("producer") or "—"),
        ("Line", sale.get("line", "—")), ("Carrier", sale.get("carrier") or "—"),
        ("Type", sale.get("type", "—")), ("Status", sale.get("status", "—")),
        ("Premium", money(sale.get("premium"))), ("Commission", money(sale.get("commission"))),
        ("Date", sale.get("date", "—")), ("Notes", sale.get("notes") or "—"),
    ]
    tr = "".join(
        f'<tr><td style="padding:9px 14px;color:{BRAND_MUTED};font:13px Arial;border-bottom:1px solid {BRAND_BORDER};white-space:nowrap">{k}</td>'
        f'<td style="padding:9px 14px;color:{BRAND_TEXT};font:600 14px Arial;border-bottom:1px solid {BRAND_BORDER}">{v}</td></tr>'
        for k, v in rows
    )
    return f"""\
<div style="background:{BRAND_LIGHT_BG};padding:24px;font-family:Arial,Helvetica,sans-serif">
  <div style="max-width:560px;margin:0 auto;background:{BRAND_WHITE};border-radius:14px;overflow:hidden;box-shadow:0 2px 12px rgba(0,174,239,0.10)">
    <div style="background:{BRAND_DARK};padding:20px 24px">
      <span style="display:inline-block;width:34px;height:34px;border-radius:9px;background:{BRAND_BLUE};
                   color:{BRAND_DARK};font:700 18px/34px Georgia;text-align:center;margin-right:10px">W</span>
      <span style="color:{BRAND_WHITE};font:600 17px Arial">{agency}</span></div>
    <div style="padding:22px 24px 4px">
      <div style="font:600 20px Georgia;color:{BRAND_DARK}">New sale logged</div>
      <div style="font:14px Arial;color:{BRAND_MUTED};margin-top:4px">{money(sale.get('commission'))} commission on {money(sale.get('premium'))} premium.</div>
    </div>
    <table style="width:100%;border-collapse:collapse;margin:14px 0 8px">{tr}</table>
    <div style="padding:14px 24px 22px;color:{BRAND_MUTED};font:12px Arial">Sent automatically by the {agency} sales tracker.</div>
  </div></div>"""


def dispatch_email(recipients, subject, text_body, html_body, reply_to):
    if EMAIL_BACKEND == "smtp":
        msg = MIMEMultipart("alternative")
        msg["Subject"], msg["From"], msg["To"] = subject, formataddr((FROM_NAME, FROM_EMAIL)), ", ".join(recipients)
        if reply_to:
            msg["Reply-To"] = reply_to
        msg.attach(MIMEText(text_body, "plain"))
        msg.attach(MIMEText(html_body, "html"))
        with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=20) as server:
            if SMTP_TLS:
                server.starttls()
            if SMTP_USER:
                server.login(SMTP_USER, SMTP_PASS)
            server.sendmail(FROM_EMAIL, recipients, msg.as_string())
    elif EMAIL_BACKEND == "sendgrid":
        payload = {
            "personalizations": [{"to": [{"email": r} for r in recipients]}],
            "from": {"email": FROM_EMAIL, "name": FROM_NAME},
            "subject": subject,
            "content": [{"type": "text/plain", "value": text_body}, {"type": "text/html", "value": html_body}],
        }
        if reply_to:
            payload["reply_to"] = {"email": reply_to}
        req = urllib.request.Request(
            "https://api.sendgrid.com/v3/mail/send", data=json.dumps(payload).encode(),
            headers={"Authorization": f"Bearer {SENDGRID_KEY}", "Content-Type": "application/json"}, method="POST")
        urllib.request.urlopen(req, timeout=20)
    else:
        log.info("[console] to=%s subject=%s\n%s", recipients, subject, text_body)


@app.post("/api/notify")
@login_required
def notify():
    data = request.get_json(silent=True) or {}
    recipients = parse_recipients(data.get("notify"))
    if not recipients:
        return jsonify(ok=False, error="no recipients"), 400
    sale = data.get("sale", {}) or {}
    agency = data.get("agency", "We Insure Things")
    subject = data.get("subject") or f"New sale: {sale.get('customer', 'Unknown')}"
    text_body = data.get("body") or json.dumps(sale, indent=2)
    html_body = build_html(sale, agency, text_body)
    try:
        dispatch_email(recipients, subject, text_body, html_body, data.get("from", ""))
        return jsonify(ok=True, sent_to=recipients)
    except Exception as exc:                       # noqa: BLE001
        log.exception("email send failed")
        return jsonify(ok=False, error=str(exc)), 502


# --------------------------------------------------------------------------- #
# Per-user preferences (e.g. a producer's own monthly goal)
# --------------------------------------------------------------------------- #
@app.get("/api/prefs")
@login_required
def prefs_get():
    me = current_user()["email"]
    row = db().execute("SELECT value FROM prefs WHERE email=?", (me,)).fetchone()
    return jsonify(value=json.loads(row["value"]) if row else {})


@app.put("/api/prefs")
@login_required
def prefs_put():
    me = current_user()["email"]
    val = json.dumps((request.get_json(silent=True) or {}).get("value", {}))
    db().execute("INSERT INTO prefs(email,value) VALUES(?,?) ON CONFLICT(email) DO UPDATE SET value=excluded.value", (me, val))
    db().commit()
    return jsonify(ok=True)


# --------------------------------------------------------------------------- #
# Reporting — dashboard math as SQL aggregates (scales to thousands of rows)
# --------------------------------------------------------------------------- #
def _period_bounds(period, frm, to):
    today = datetime.now().date()
    if period == "YTD":
        return f"{today.year}-01-01", today.isoformat()
    if period == "ALL":
        return "0000-01-01", "9999-12-31"
    if period == "CUSTOM" and frm and to:
        return frm, to
    # MTD (default)
    return today.replace(day=1).isoformat(), today.isoformat()


def _scope_clause(scope):
    if scope == "mine":
        return " AND created_by=?", [current_user()["email"]]
    return "", []


@app.get("/api/report/summary")
@login_required
def report_summary():
    scope = request.args.get("scope", "agency")
    sc, sp = _scope_clause(scope)
    today = datetime.now().date()
    mkey = today.strftime("%Y-%m")
    lkey = (today.replace(day=1) - timedelta(days=1)).strftime("%Y-%m")
    days_in_month = (today.replace(day=1) + timedelta(days=32)).replace(day=1) - timedelta(days=1)
    days_in_month = days_in_month.day

    def total(where, params):
        row = db().execute(f"SELECT COALESCE(SUM(premium),0) p, COUNT(*) c FROM sales WHERE status='Bound'{sc}{where}", sp + params).fetchone()
        return row["p"], row["c"]

    mtd, mtd_n   = total(" AND substr(date,1,7)=?", [mkey])
    today_p, _   = total(" AND date=?", [today.isoformat()])
    last_p, _    = total(" AND substr(date,1,7)=?", [lkey])

    # goal: agency goal from settings, or the producer's own goal from prefs
    grow = db().execute("SELECT value FROM settings WHERE id='agency'").fetchone()
    agency_goal = (json.loads(grow["value"]).get("monthlyGoal") if grow else 0) or 0
    goal = agency_goal
    if scope == "mine":
        prow = db().execute("SELECT value FROM prefs WHERE email=?", (current_user()["email"],)).fetchone()
        mine_goal = (json.loads(prow["value"]).get("goal") if prow else 0) or 0
        goal = mine_goal or 0

    return jsonify(
        scope=scope, goal=goal, daysInMonth=days_in_month, day=today.day,
        mtdPremium=mtd, mtdCount=mtd_n, todayPremium=today_p, lastMonthPremium=last_p,
    )


@app.get("/api/report/leaderboard")
@login_required
def report_leaderboard():
    metric = request.args.get("metric", "premium")
    scope = request.args.get("scope", "agency")
    btype = request.args.get("type", "")
    carrier = request.args.get("carrier", "")
    start, end = _period_bounds(request.args.get("period", "MTD"), request.args.get("from"), request.args.get("to"))
    sc, params = _scope_clause(scope)
    agg = {"premium": "COALESCE(SUM(premium),0)", "policies": "COUNT(*)", "revenue": "COALESCE(SUM(commission),0)"}.get(metric, "COALESCE(SUM(premium),0)")
    where = " AND date>=? AND date<=?"
    args = params + [start, end]
    if btype:
        where += " AND type=?"; args.append(btype)
    if carrier:
        where += " AND carrier=?"; args.append(carrier)
    rows = db().execute(
        f"SELECT COALESCE(NULLIF(producer,''),'Unassigned') AS producer, {agg} AS value "
        f"FROM sales WHERE status='Bound'{sc}{where} GROUP BY producer ORDER BY value DESC", args).fetchall()
    totals = db().execute(
        f"SELECT COALESCE(SUM(premium),0) p, COUNT(*) c, COALESCE(SUM(commission),0) r "
        f"FROM sales WHERE status='Bound'{sc}{where}", args).fetchone()
    return jsonify(metric=metric,
                   rows=[{"producer": r["producer"], "value": r["value"]} for r in rows],
                   totals={"premium": totals["p"], "policies": totals["c"], "revenue": totals["r"]})


# --------------------------------------------------------------------------- #
# Integrations status + NowCerts push
# --------------------------------------------------------------------------- #
@app.get("/api/integrations")
@login_required
def integrations():
    return jsonify(nowcerts=NC_ENABLED)


def _nc_get_token():
    """Fetch & cache a NowCerts bearer token (password grant)."""
    import time
    if _nc_token["value"] and _nc_token["exp"] > time.time() + 60:
        return _nc_token["value"]
    data = urllib.parse.urlencode({
        "username": NC_USERNAME, "password": NC_PASSWORD,
        "grant_type": "password", "client_id": "ngAuthApp",
    }).encode()
    req = urllib.request.Request(f"{NC_BASE}/token", data=data,
                                 headers={"Content-Type": "application/x-www-form-urlencoded"}, method="POST")
    with urllib.request.urlopen(req, timeout=25) as resp:
        body = json.loads(resp.read())
    _nc_token["value"] = body["access_token"]
    _nc_token["exp"] = time.time() + int(body.get("expires_in", 3600))
    return _nc_token["value"]


def _nc_split_name(sale):
    """NowCerts wants commercialName OR first/last. Personal lines → split; else commercial."""
    name = (sale.get("customer") or "").strip()
    personal = sale.get("line") in ("Auto", "Home", "Renters", "Life", "Health", "Umbrella", "Bundle (Auto+Home)")
    parts = name.split()
    if personal and len(parts) >= 2:
        return {"firstName": parts[0], "lastName": " ".join(parts[1:]), "type": 1}  # 1 = Personal
    return {"commercialName": name, "type": 0}  # 0 = Commercial


def agency_settings():
    row = db().execute("SELECT value FROM settings WHERE id='agency'").fetchone()
    return json.loads(row["value"]) if row else {}


def nc_push_sale(sale, settings=None):
    """Push one bound sale to NowCerts as an insured + policy. Returns (insured_id, policy_id, url)."""
    settings = settings or {}
    lob_map = settings.get("nowcertsLobMap") or {}
    token = _nc_get_token()
    insured = _nc_split_name(sale)
    insured_name = sale.get("customer") or ""
    rate = sale.get("rate")
    comm_pct = float(rate) if rate not in (None, "") else None
    lob = lob_map.get(sale.get("line")) or NC_LOB_MAP.get(sale.get("line")) or sale.get("line")   # settings map → defaults → as-is
    policy = {
        "number": sale.get("id"),
        "insuredName": insured_name,
        "lineOfBusinessName": lob,
        "carrierName": sale.get("carrier"),
        "premium": float(sale.get("premium") or 0),
        "effectiveDate": (sale.get("date") or datetime.now().date().isoformat()) + "T00:00:00",
        "bindDate": (sale.get("date") or datetime.now().date().isoformat()) + "T00:00:00",
        "businessType": 0,
        "isPolicyRenewal": sale.get("type") == "Renewal",
        "checkPolicyOnNumber": True,
    }
    if comm_pct is not None:
        policy["agencyCommissionPercent"] = comm_pct
    body = {**insured, "eMail": "", "active": True, "policies": [policy]}
    req = urllib.request.Request(f"{NC_BASE}/api/InsuredAndPolicies/Insert",
                                 data=json.dumps(body).encode(),
                                 headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
                                 method="POST")
    with urllib.request.urlopen(req, timeout=30) as resp:
        result = json.loads(resp.read())
    if str(result.get("status", "")).lower() in ("error", "1", "2"):
        raise RuntimeError(result.get("message") or "NowCerts rejected the record")
    pol = (result.get("policiesOrQuotes") or [{}])[0]
    return result.get("insuredDatabaseId"), pol.get("policyOrQuoteId"), pol.get("objectURL")


def nc_get(path):
    token = _nc_get_token()
    req = urllib.request.Request(f"{NC_BASE}{path}", headers={"Authorization": f"Bearer {token}"})
    with urllib.request.urlopen(req, timeout=25) as resp:
        return json.loads(resp.read())


def _labels(data, keys):
    """Best-effort: pull display strings from an unknown list/wrapped-list response."""
    items = data.get("data") if isinstance(data, dict) else data
    out = []
    if isinstance(items, list):
        for it in items:
            if isinstance(it, str):
                out.append(it)
            elif isinstance(it, dict):
                for k in keys:
                    if it.get(k):
                        out.append(str(it[k])); break
    return sorted(set(out))


@app.get("/api/nowcerts/meta")
@login_required
def nowcerts_meta():
    if not NC_ENABLED:
        return jsonify(lob=[], carriers=[])
    lob, carriers = [], []
    try: lob = _labels(nc_get("/api/LineOfBusinessList?key="), ["name", "text", "lineOfBusinessName", "lineOfBusiness", "value"])
    except Exception: pass
    try: carriers = _labels(nc_get("/api/CarrierDetailList?key="), ["name", "carrierName", "text", "value"])
    except Exception: pass
    return jsonify(lob=lob, carriers=carriers)


@app.post("/api/nowcerts/test")
@login_required
def nowcerts_test():
    """Verify NowCerts credentials with a token fetch + heartbeat (no data written)."""
    if not NC_ENABLED:
        return jsonify(ok=False, error="NowCerts is not configured on the server"), 400
    try:
        nc_get("/api/heartbeat")
        return jsonify(ok=True)
    except Exception as exc:                       # noqa: BLE001
        return jsonify(ok=False, error=str(exc)), 502


@app.post("/api/sales/<sid>/push-nowcerts")
@login_required
def sales_push_nowcerts(sid):
    if not NC_ENABLED:
        return jsonify(ok=False, error="NowCerts is not configured on the server"), 400
    row = db().execute("SELECT * FROM sales WHERE id=?", (sid,)).fetchone()
    if not row:
        return jsonify(ok=False, error="not found"), 404
    sale = sale_to_dict(row)
    try:
        insured_id, policy_id, url = nc_push_sale(sale, agency_settings())
    except Exception as exc:                       # noqa: BLE001
        log.exception("NowCerts push failed")
        return jsonify(ok=False, error=str(exc)), 502
    db().execute("UPDATE sales SET nc_insured_id=?, nc_policy_id=?, nc_pushed_at=? WHERE id=?",
                 (insured_id, policy_id, now_iso(), sid))
    audit("push-nowcerts", "sale", sid, f"insured {insured_id}")
    db().commit()
    return jsonify(ok=True, insuredId=insured_id, policyId=policy_id, url=url)


# --------------------------------------------------------------------------- #
# Serve the SPA
# --------------------------------------------------------------------------- #
@app.get("/")
def index():
    return send_file(os.path.abspath(INDEX_PATH))


@app.get("/health")
def health():
    return jsonify(ok=True, configured=bool(CLIENT_ID), email_backend=EMAIL_BACKEND)


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=8093, debug=False)


# --------------------------------------------------------------------------- #
# Deploy alongside WIT-FM
# --------------------------------------------------------------------------- #
# /etc/wit-app.env  (chmod 600):
#   WIT_GOOGLE_CLIENT_ID=xxxx.apps.googleusercontent.com
#   WIT_ALLOWED_DOMAINS=weinsurethings.com
#   WIT_SECRET_KEY=<64 hex chars, generate once and keep stable>
#   WIT_COOKIE_SECURE=true
#   WIT_EMAIL_BACKEND=smtp
#   WIT_FROM_EMAIL=wit-tracker@weinsurethings.com
#   WIT_SMTP_HOST=smtp.gmail.com
#   WIT_SMTP_PORT=587
#   WIT_SMTP_USER=logan@weinsurethings.com
#   WIT_SMTP_PASS=<app password>
#   WIT_INDEX_PATH=/home/ubuntu/witradio/wit-sales-tracker.html
#   WIT_DB_PATH=/home/ubuntu/witradio/wit_tracker.db
#
# /etc/systemd/system/wit-app.service:
#   [Unit]
#   Description=WIT Sales Tracker
#   After=network.target
#   [Service]
#   EnvironmentFile=/etc/wit-app.env
#   WorkingDirectory=/home/ubuntu/witradio
#   ExecStart=/usr/bin/gunicorn -w 2 -b 127.0.0.1:8093 wit_app:app
#   Restart=always
#   [Install]
#   WantedBy=multi-user.target
#   ->  sudo systemctl enable --now wit-app
#
# nginx — a SEPARATE server block keeps it cleanly apart from the radio:
#   server {
#       listen 443 ssl;
#       server_name sales.weinsurethings.com;
#       ssl_certificate     /etc/letsencrypt/live/sales.weinsurethings.com/fullchain.pem;
#       ssl_certificate_key /etc/letsencrypt/live/sales.weinsurethings.com/privkey.pem;
#       location / { proxy_pass http://127.0.0.1:8093; proxy_set_header Host $host;
#                    proxy_set_header X-Forwarded-Proto https; }
#   }
#   ->  sudo certbot --nginx -d sales.weinsurethings.com
#
# Google Cloud Console -> Credentials -> OAuth client (Web):
#   Authorized JavaScript origins:  https://sales.weinsurethings.com
#   (no redirect URI / secret needed for the Identity Services button)

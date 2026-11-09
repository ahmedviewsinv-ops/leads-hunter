"""
Email sender for Mirage Leads Hunter (SMTP).

Works with any mailbox that offers SMTP: Gmail (use an App Password, not the account password), Outlook,
Zoho, a company mailbox. Messages are plain text, one recipient per message, sent one by one with random
delays, a rest after every batch and a daily cap. Every message ends with an opt-out line.

SMTP settings are stored in settings.json next to this file (the password is stored there too).
"""
import json
import os
import random
import smtplib
import threading
import time
from email.message import EmailMessage
from email.utils import formataddr, formatdate, make_msgid

HERE = os.path.dirname(os.path.abspath(__file__))
SETTINGS_PATH = os.path.join(HERE, "settings.json")
MIN_DELAY_FLOOR = 5

PRESETS = {
    "gmail": {"host": "smtp.gmail.com", "port": 587, "security": "starttls"},
    "outlook": {"host": "smtp.office365.com", "port": 587, "security": "starttls"},
    "zoho": {"host": "smtp.zoho.com", "port": 587, "security": "starttls"},
}


def load_settings():
    try:
        with open(SETTINGS_PATH, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_settings(new):
    cur = load_settings()
    for k in ("host", "port", "security", "user", "from_name", "from_email", "reply_to", "footer"):
        if k in new:
            cur[k] = new[k]
    if new.get("password"):  # an empty password keeps the saved one
        cur["password"] = new["password"]
    with open(SETTINGS_PATH, "w", encoding="utf-8") as f:
        json.dump(cur, f, ensure_ascii=False, indent=2)
    return cur


def public_settings():
    cur = dict(load_settings())
    cur["has_password"] = bool(cur.pop("password", ""))
    return cur


def connect(cfg):
    host, port = cfg.get("host", ""), int(cfg.get("port") or 587)
    if not host or not cfg.get("user") or not cfg.get("password"):
        raise ValueError("SMTP host, user and password are required")
    if cfg.get("security") == "ssl":
        srv = smtplib.SMTP_SSL(host, port, timeout=30)
    else:
        srv = smtplib.SMTP(host, port, timeout=30)
        srv.ehlo()
        if cfg.get("security", "starttls") == "starttls":
            srv.starttls()
            srv.ehlo()
    srv.login(cfg["user"], cfg["password"])
    return srv


def build(cfg, to, subject, body):
    msg = EmailMessage()
    from_email = cfg.get("from_email") or cfg["user"]
    msg["From"] = formataddr((cfg.get("from_name", ""), from_email))
    msg["To"] = to
    msg["Subject"] = subject
    msg["Date"] = formatdate(localtime=True)
    msg["Message-ID"] = make_msgid(domain=from_email.split("@")[-1])
    if cfg.get("reply_to"):
        msg["Reply-To"] = cfg["reply_to"]
    footer = (cfg.get("footer") or "").strip()
    msg.set_content(body.rstrip() + ("\n\n--\n" + footer if footer else ""))
    return msg


def send_test(to):
    cfg = load_settings()
    srv = connect(cfg)
    try:
        srv.send_message(build(cfg, to, "Mirage Leads Hunter: test email", "If you can read this, SMTP works."))
    finally:
        try:
            srv.quit()
        except Exception:
            pass


class EmailSender:
    def __init__(self, mark_contacted, log_result, sent_today):
        self.mark_contacted = mark_contacted  # fn(lead_id)
        self.log_result = log_result          # fn(lead_id, email, ok, note)
        self.sent_today = sent_today          # fn() -> int
        self.lock = threading.Lock()
        self.stop = threading.Event()
        self.thread = None
        self.s = self._fresh()

    @staticmethod
    def _fresh():
        return {"status": "idle", "sent": 0, "failed": 0, "total": 0, "index": 0, "current": "",
                "next_at": 0, "note": "", "entries": []}

    def running(self):
        return self.thread is not None and self.thread.is_alive()

    def start(self, items, subject, cfg):
        """items: [{id, email, body}]. Returns False when a run is already active."""
        if self.running():
            return False
        self.stop.clear()
        with self.lock:
            self.s = self._fresh()
            self.s.update(status="sending", total=len(items))
        self.thread = threading.Thread(target=self._run, args=(items, subject, cfg), daemon=True)
        self.thread.start()
        return True

    def halt(self):
        self.stop.set()

    def snapshot(self, since=0):
        with self.lock:
            s = dict(self.s)
        entries = s.pop("entries")
        s["entries"] = entries[since:]
        s["next"] = len(entries)
        s["next_in"] = max(0, int(s["next_at"] - time.time())) if s["next_at"] else 0
        return s

    def _set(self, **kw):
        with self.lock:
            self.s.update(kw)

    def _entry(self, email, ok, note):
        with self.lock:
            self.s["entries"].append({"email": email, "ok": ok, "note": note})
            self.s["sent" if ok else "failed"] += 1

    def _run(self, items, subject, cfg):
        smtp_cfg = load_settings()
        try:
            srv = connect(smtp_cfg)
        except Exception as exc:
            self._set(status="error", note=str(exc)[:200])
            return
        final, sent_in_run = "done", 0
        try:
            for i, it in enumerate(items):
                if self.stop.is_set():
                    final = "stopped"
                    break
                if self.sent_today() >= cfg["daily_cap"]:
                    final = "daily_cap"
                    break
                self._set(index=i, current=it["email"], status="sending", next_at=0)
                ok, note = True, ""
                try:
                    srv.send_message(build(smtp_cfg, it["email"], subject, it["body"]))
                except smtplib.SMTPServerDisconnected:
                    try:  # one reconnect, then try this message again
                        srv = connect(smtp_cfg)
                        srv.send_message(build(smtp_cfg, it["email"], subject, it["body"]))
                    except Exception as exc:
                        ok, note = False, str(exc)[:120]
                except smtplib.SMTPRecipientsRefused:
                    ok, note = False, "address refused"
                except smtplib.SMTPAuthenticationError:
                    self._set(status="error", note="Login failed. For Gmail use an App Password.")
                    return
                except Exception as exc:
                    ok, note = False, str(exc)[:120]
                self.log_result(it["id"], it["email"], ok, note)
                if ok:
                    self.mark_contacted(it["id"])
                    sent_in_run += 1
                self._entry(it["email"], ok, note)
                if i == len(items) - 1:
                    break
                delay = random.uniform(cfg["min_delay"], cfg["max_delay"]) if ok else 2
                if ok and cfg["batch_size"] > 0 and sent_in_run % cfg["batch_size"] == 0:
                    delay += cfg["batch_pause"] * 60
                self._set(status="waiting", next_at=time.time() + delay)
                end = time.time() + delay
                while time.time() < end and not self.stop.is_set():
                    time.sleep(1)
        finally:
            try:
                srv.quit()
            except Exception:
                pass
        self._set(status=final, next_at=0)

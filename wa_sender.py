"""
WhatsApp sender for Mirage Leads Hunter.

It works like DoDo WA Sender: a browser window is signed in to WhatsApp Web with the phone number you want to
send from, and messages are sent one by one by opening the chat link and pressing send.

The difference from the first version: the account is connected FIRST, from the dashboard.
    1. Press "Connect WhatsApp". A Chrome window opens on web.whatsapp.com and the QR code is also shown
       in the dashboard.
    2. On the phone: WhatsApp > Linked devices > Link a device > scan the QR code.
    3. The dashboard shows the connected number. Sending is only possible while an account is connected.
The login is kept in the wa_profile folder, so the next start reconnects without a QR code.
"Switch number" signs out and shows a new QR code.

All browser work runs in one background thread (Playwright needs that).
"""
import base64
import queue
import random
import shutil
import threading
import time
import urllib.parse

MIN_DELAY_FLOOR = 10  # seconds: the dashboard cannot go below this

READY_JS = "() => !!document.querySelector('#pane-side, #side')"

ACCOUNT_JS = r"""() => {
  try {
    const v = localStorage.getItem('last-wid-md') || localStorage.getItem('last-wid') || '';
    const m = String(v).replace(/"/g, '').match(/^(\d+)/);
    return m ? m[1] : '';
  } catch (e) { return ''; }
}"""

STATE_JS = r"""() => {
  const main = document.querySelector('#main');
  const comp = main && (main.querySelector('footer [contenteditable="true"]') || main.querySelector('[contenteditable="true"]'));
  const text = comp ? (comp.innerText || '').replace(/​/g, '').trim() : '';
  const send = !!main && [...main.querySelectorAll('[data-icon]')].some(e => /send/i.test(e.getAttribute('data-icon') || ''));
  const dlg = !!document.querySelector('div[role="dialog"], div[data-animate-modal-popup="true"]');
  const pending = !!(main && main.querySelector('span[data-icon="msg-time"]'));
  return { main: !!main, hasText: text.length > 0, send: send, dlg: dlg, pending: pending };
}"""

OPEN_JS = r"""(url) => {
  const a = document.createElement('a');
  a.href = url; a.target = '_self'; a.style.display = 'none';
  (document.querySelector('#app') || document.body).appendChild(a);
  a.click();
  setTimeout(() => a.remove(), 1000);
}"""

CLICK_SEND_JS = r"""() => {
  const main = document.querySelector('#main');
  if (!main) return false;
  const icons = [...main.querySelectorAll('[data-icon]')].filter(e => /send/i.test(e.getAttribute('data-icon') || ''));
  const ic = icons[icons.length - 1];
  if (!ic) return false;
  (ic.closest('button,[role="button"]') || ic).click();
  return true;
}"""

FOCUS_COMPOSER_JS = r"""() => {
  const main = document.querySelector('#main');
  const c = main && (main.querySelector('footer [contenteditable="true"]') || main.querySelector('[contenteditable="true"]'));
  if (c) c.focus();
  return !!c;
}"""

DISMISS_JS = r"""() => {
  const d = document.querySelector('div[role="dialog"], div[data-animate-modal-popup="true"]');
  if (d) { const b = d.querySelector('button,[role="button"]'); if (b) b.click(); }
}"""

QR_SELECTORS = ("div[data-ref] canvas", "canvas[aria-label]", "[data-testid='qrcode'] canvas", "canvas")


class WindowClosed(Exception):
    pass


class WaSender:
    def __init__(self, profile_dir, mark_contacted, log_result, sent_today):
        self.profile_dir = profile_dir
        self.mark_contacted = mark_contacted  # fn(lead_id)
        self.log_result = log_result          # fn(lead_id, phone, ok, note)
        self.sent_today = sent_today          # fn() -> int
        self.lock = threading.Lock()
        self.stop = threading.Event()
        self.q = queue.Queue()
        self.thread = None
        self.c = {"conn": "off", "account": "", "qr": "", "note": ""}
        self.s = self._fresh()

    @staticmethod
    def _fresh():
        return {"status": "idle", "sent": 0, "failed": 0, "total": 0, "index": 0,
                "current": "", "next_at": 0, "snote": "", "entries": []}

    # ---------------------------------------------------------------- public API
    def _ensure_thread(self):
        if self.thread is None or not self.thread.is_alive():
            self.thread = threading.Thread(target=self._loop, daemon=True)
            self.thread.start()

    def connect(self):
        with self.lock:
            if self.c["conn"] in ("qr", "connected", "starting"):
                return
            self.c.update(conn="starting", note="", qr="")
        self._ensure_thread()
        self.q.put(("connect",))

    def disconnect(self):
        self.stop.set()
        self.q.put(("disconnect",))

    def logout(self):
        self.stop.set()
        self.q.put(("logout",))

    def sending(self):
        return self.s["status"] in ("sending", "waiting")

    def start(self, items, cfg):
        """Returns 'ok', 'not_connected' or 'busy'."""
        if self.c["conn"] != "connected":
            return "not_connected"
        if self.sending():
            return "busy"
        self.stop.clear()
        with self.lock:
            self.s = self._fresh()
            self.s.update(status="sending", total=len(items))
        self.q.put(("send", items, cfg))
        return "ok"

    def halt(self):
        self.stop.set()

    def snapshot(self, since=0):
        with self.lock:
            out = dict(self.c)
            s = dict(self.s)
        entries = s.pop("entries")
        out.update(s)
        if out["conn"] != "qr":
            out["qr"] = ""
        out["entries"] = entries[since:]
        out["next"] = len(entries)
        out["next_in"] = max(0, int(out["next_at"] - time.time())) if out["next_at"] else 0
        return out

    # ---------------------------------------------------------------- state helpers
    def _conn(self, **kw):
        with self.lock:
            self.c.update(kw)

    def _set(self, **kw):
        with self.lock:
            self.s.update(kw)

    def _entry(self, phone, ok, note):
        with self.lock:
            self.s["entries"].append({"phone": phone, "ok": ok, "note": note})
            self.s["sent" if ok else "failed"] += 1

    # ---------------------------------------------------------------- browser thread
    def _launch(self, pw):
        kw = dict(user_data_dir=self.profile_dir, headless=False, viewport=None,
                  args=["--disable-blink-features=AutomationControlled"])
        try:
            return pw.chromium.launch_persistent_context(channel="chrome", **kw)  # the Chrome already installed
        except Exception:
            return pw.chromium.launch_persistent_context(**kw)  # Playwright's own Chromium

    def _qr(self, page):
        for sel in QR_SELECTORS:
            try:
                el = page.query_selector(sel)
                if el and el.is_visible():
                    png = el.screenshot()
                    return "data:image/png;base64," + base64.b64encode(png).decode()
            except Exception:
                continue
        return ""

    def _poll(self, page):
        if page.is_closed():
            raise WindowClosed()
        if page.evaluate(READY_JS):
            acct = page.evaluate(ACCOUNT_JS)
            self._conn(conn="connected", qr="", note="", account=acct or self.c["account"])
        else:
            qr = self._qr(page)
            self._conn(conn="qr" if qr else "starting", qr=qr, account="")

    def _close(self, ctx):
        try:
            if ctx:
                ctx.close()
        except Exception:
            pass

    def _loop(self):
        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            self._conn(conn="error", note="Playwright is not installed. Run: pip install playwright", qr="")
            return
        ctx = page = None
        try:
            with sync_playwright() as pw:
                while True:
                    try:
                        cmd = self.q.get(timeout=2)
                    except queue.Empty:
                        cmd = None
                    try:
                        if cmd and cmd[0] == "connect" and ctx is None:
                            ctx = self._launch(pw)
                            page = ctx.pages[0] if ctx.pages else ctx.new_page()
                            page.on("dialog", lambda d: d.accept())
                            page.goto("https://web.whatsapp.com", wait_until="domcontentloaded")
                        elif cmd and cmd[0] in ("disconnect", "logout"):
                            self._close(ctx)
                            ctx = page = None
                            if cmd[0] == "logout":
                                shutil.rmtree(self.profile_dir, ignore_errors=True)
                            self._conn(conn="off", qr="", account="", note="")
                            self._set(status="idle", next_at=0)
                            continue
                        elif cmd and cmd[0] == "send" and ctx is not None:
                            self._send(page, cmd[1], cmd[2])
                        if ctx is not None:
                            self._poll(page)
                    except WindowClosed:
                        self._close(ctx)
                        ctx = page = None
                        self._conn(conn="off", qr="", account="", note="The Chrome window was closed")
                        if self.sending():
                            self._set(status="stopped", next_at=0)
                    except Exception as exc:
                        self._close(ctx)
                        ctx = page = None
                        self._conn(conn="error", qr="", account="", note=str(exc).splitlines()[0][:200])
                        if self.sending():
                            self._set(status="error", snote="connection lost", next_at=0)
        finally:
            self._close(ctx)

    # ---------------------------------------------------------------- sending
    def _wait(self, fn, timeout, step=0.5):
        t = time.time()
        while time.time() - t < timeout:
            if self.stop.is_set():
                return False
            try:
                if fn():
                    return True
            except Exception:
                pass
            time.sleep(step)
        return False

    def _open_chat(self, page, phone, text):
        url = "https://web.whatsapp.com/send?phone=%s&text=%s" % (phone, urllib.parse.quote(text))
        for attempt in (1, 2):
            if attempt == 1:
                page.evaluate(OPEN_JS, url)
            else:
                page.goto(url, wait_until="domcontentloaded")
            t = time.time()
            while time.time() - t < (20 if attempt == 1 else 30):
                if self.stop.is_set():
                    return "stopped"
                if page.is_closed():
                    raise WindowClosed()
                st = page.evaluate(STATE_JS)
                if (st["hasText"] or st["send"]) and not st["dlg"]:
                    return "ok"
                if st["dlg"]:
                    time.sleep(1.2)
                    st = page.evaluate(STATE_JS)
                    if not (st["hasText"] or st["send"]):
                        page.evaluate(DISMISS_JS)
                        return "invalid"
                time.sleep(0.4)
        return "timeout"

    def _send_current(self, page):
        time.sleep(random.uniform(0.8, 1.6))
        page.evaluate(CLICK_SEND_JS)
        time.sleep(2.5)
        if page.evaluate(STATE_JS)["hasText"]:  # the click did not send: try Enter
            if page.evaluate(FOCUS_COMPOSER_JS):
                page.keyboard.press("Enter")
                time.sleep(2.5)
        if page.evaluate(STATE_JS)["hasText"]:
            return False
        t = time.time()
        while time.time() - t < 15 and page.evaluate(STATE_JS)["pending"]:
            time.sleep(0.5)
        return True

    def _send(self, page, items, cfg):
        final, sent_in_run = "done", 0
        try:
            for i, it in enumerate(items):
                if self.stop.is_set():
                    final = "stopped"
                    break
                if self.sent_today() >= cfg["daily_cap"]:
                    final = "daily_cap"
                    break
                self._set(index=i, current=it["phone"], status="sending", next_at=0)
                res = self._open_chat(page, it["phone"], it["text"])
                if res == "stopped":
                    final = "stopped"
                    break
                if res == "ok":
                    ok = self._send_current(page)
                    note = "" if ok else "message not sent"
                else:
                    ok = False
                    note = "number not on WhatsApp" if res == "invalid" else "timeout"
                self.log_result(it["id"], it["phone"], ok, note)
                if ok:
                    self.mark_contacted(it["id"])
                    sent_in_run += 1
                self._entry(it["phone"], ok, note)
                if i == len(items) - 1:
                    break
                delay = random.uniform(cfg["min_delay"], cfg["max_delay"]) if ok else 3
                if ok and cfg["batch_size"] > 0 and sent_in_run % cfg["batch_size"] == 0:
                    delay += cfg["batch_pause"] * 60
                self._set(status="waiting", next_at=time.time() + delay)
                end = time.time() + delay
                while time.time() < end and not self.stop.is_set():
                    time.sleep(1)
        except WindowClosed:
            raise
        except Exception as exc:
            self._set(status="error", snote=str(exc).splitlines()[0][:200], next_at=0)
            return
        self._set(status=final, next_at=0)

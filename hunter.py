"""
Mirage Leads Hunter - backend.

Searches the web (free by default through DuckDuckGo, no key needed; optional SERPAPI_KEY
or GOOGLE_API_KEY + GOOGLE_CX), visits each result site, extracts company, phones, email,
city, scores the leads, stores them in SQLite and serves the dashboard (index.html) plus a JSON API.

Run:
    pip install -r requirements.txt
    python hunter.py serve            # dashboard at http://127.0.0.1:5000
    python hunter.py hunt --keywords "شركات خدمات" --countries SA AE --target 1000
"""
import argparse
import csv
import io
import json
import os
import re
import smtplib
import sqlite3
import sys
import threading
import time
import urllib.parse
import urllib.robotparser
import uuid
from concurrent.futures import ThreadPoolExecutor

import requests
from bs4 import BeautifulSoup

try:
    import phonenumbers
except ImportError:  # phone validation degrades to a regex check
    phonenumbers = None

HERE = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.environ.get("MIRAGE_DB", os.path.join(HERE, "leads.db"))
UA = "MirageLeadsHunter/1.1 (+business-directory research; respects robots.txt)"
TIMEOUT = 12
PER_DOMAIN_DELAY = 1.5      # seconds between requests to the same site
WORKERS = 12                # sites fetched in parallel
MAX_PHONES_PER_SITE = 3     # numbers kept from one site (mobile numbers first)
SITE_CAP_FACTOR = 20        # a job gives up after scanning target x 20 sites

# Any country works: add a row here (ISO code, Arabic name, English name, cities).
COUNTRIES = {
    "SA": ("السعودية", "Saudi Arabia", ["الرياض", "جدة", "مكة", "المدينة المنورة", "الدمام", "الخبر", "الظهران", "الطائف",
                                       "تبوك", "بريدة", "أبها", "خميس مشيط", "حائل", "الجبيل", "ينبع", "نجران", "جازان",
                                       "الأحساء", "القطيف", "الخرج"]),
    "AE": ("الإمارات", "United Arab Emirates", ["دبي", "أبوظبي", "الشارقة", "عجمان", "رأس الخيمة", "الفجيرة", "أم القيوين",
                                               "العين"]),
    "EG": ("مصر", "Egypt", ["القاهرة", "الإسكندرية", "الجيزة", "المنصورة", "طنطا", "أسيوط", "الأقصر", "أسوان", "بورسعيد",
                           "السويس", "الإسماعيلية", "الزقازيق", "6 أكتوبر", "العاشر من رمضان", "التجمع الخامس", "الغردقة"]),
    "KW": ("الكويت", "Kuwait", ["الكويت", "حولي", "الفروانية", "السالمية", "الجهراء", "الأحمدي"]),
    "QA": ("قطر", "Qatar", ["الدوحة", "الريان", "الوكرة", "الخور", "الشمال"]),
    "BH": ("البحرين", "Bahrain", ["المنامة", "المحرق", "الرفاع", "مدينة عيسى"]),
    "OM": ("عمان", "Oman", ["مسقط", "صلالة", "صحار", "نزوى", "صور"]),
    "JO": ("الأردن", "Jordan", ["عمّان", "إربد", "الزرقاء", "العقبة", "السلط"]),
    "MA": ("المغرب", "Morocco", ["الدار البيضاء", "الرباط", "مراكش", "طنجة", "فاس", "أكادير"]),
    "TR": ("تركيا", "Turkey", ["إسطنبول", "أنقرة", "إزمير", "أنطاليا", "بورصة"]),
    "GB": ("بريطانيا", "United Kingdom", ["لندن", "مانشستر", "برمنغهام", "ليدز"]),
    "US": ("أمريكا", "United States", ["New York", "Los Angeles", "Houston", "Chicago", "Miami"]),
}

# After the user's own keywords are used up, the hunt widens with related service types.
SERVICES = [
    "شركة تنظيف", "شركة صيانة", "شركة نقل عفش", "شركة مكافحة حشرات", "شركة تكييف", "شركة مقاولات", "شركة ديكور",
    "شركة تسويق", "شركة تصميم مواقع", "شركة شحن", "شركة أمن وحراسة", "شركة سباكة", "شركة كهرباء", "شركة نجارة",
    "شركة تأجير سيارات", "شركة سياحة", "شركة استشارات", "شركة طباعة", "شركة تشطيبات", "شركة حدائق",
    "شركة عزل", "شركة تخليص جمركي", "مكتب محاسبة", "مكتب هندسي", "شركة تقنية معلومات",
]
# Added to each query to pull different results for the same keyword and city.
MODIFIERS = ["", "اتصل بنا", "رقم الهاتف", "واتساب", "أفضل", "أسعار", "خدمات", "تواصل معنا"]

# Directories, social networks and marketplaces: they list many companies but are not the company itself.
SKIP_DOMAINS = (
    "facebook.com", "instagram.com", "twitter.com", "x.com", "linkedin.com", "youtube.com", "tiktok.com",
    "wikipedia.org", "google.com", "maps.google", "pinterest.com", "snapchat.com", "t.me", "whatsapp.com",
)

EMAIL_RE = re.compile(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}")
PHONE_RE = re.compile(r"(?<![\w/])(\+?\d[\d\s().\-]{7,17}\d)(?![\w/])")
CONTACT_HINTS = ("contact", "اتصل", "تواصل", "about", "من-نحن", "من نحن", "عن-الشركة")
JUNK_MAIL = ("example.", "sentry", "wixpress", "domain.com", ".png", ".jpg", ".webp")


# ----------------------------------------------------------------- storage
LEADS_SQL = """CREATE TABLE leads (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company TEXT, phone TEXT, email TEXT, website TEXT, city TEXT,
    country TEXT, score INTEGER, status TEXT DEFAULT 'new', kw TEXT, created REAL,
    batch INTEGER DEFAULT 0, source TEXT DEFAULT 'web', address TEXT DEFAULT '')"""
LEAD_COLS = "company,phone,email,website,city,country,score,status,kw,created"
STATUSES = ("new", "contacted", "qualified", "demo", "optout")


def db():
    con = sqlite3.connect(DB_PATH, check_same_thread=False)
    con.row_factory = sqlite3.Row
    cols = [r[1] for r in con.execute("PRAGMA table_info(leads)")]
    if not cols:
        con.execute(LEADS_SQL)
    elif "batch" not in cols:  # older database: phone was UNIQUE. Rebuild so each search keeps its own results.
        con.execute("ALTER TABLE leads RENAME TO leads_old")
        con.execute(LEADS_SQL)
        con.execute(f"INSERT INTO leads ({LEAD_COLS},batch) SELECT {LEAD_COLS},0 FROM leads_old")
        con.execute("DROP TABLE leads_old")
    cols = [r[1] for r in con.execute("PRAGMA table_info(leads)")]
    for col, ddl in (("source", "TEXT DEFAULT 'web'"), ("address", "TEXT DEFAULT ''")):
        if col not in cols:
            con.execute(f"ALTER TABLE leads ADD COLUMN {col} {ddl}")
    con.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_batch_phone ON leads(batch, phone)")
    con.execute("CREATE TABLE IF NOT EXISTS email_log (id INTEGER PRIMARY KEY AUTOINCREMENT, lead_id INTEGER,"
                " email TEXT, ok INTEGER, note TEXT, ts REAL)")
    con.execute("CREATE TABLE IF NOT EXISTS batches (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT,"
                " created REAL, scanned INTEGER DEFAULT 0, params TEXT)")
    con.execute("CREATE TABLE IF NOT EXISTS wa_log (id INTEGER PRIMARY KEY AUTOINCREMENT, lead_id INTEGER,"
                " phone TEXT, ok INTEGER, note TEXT, ts REAL)")
    con.commit()
    return con


_db_lock = threading.Lock()


def save_lead(lead, batch=0):
    """Insert a lead. Returns the stored row dict, or None when the phone already exists."""
    with _db_lock:
        con = db()
        try:
            cur = con.execute(
                "INSERT INTO leads (company, phone, email, website, city, country, score, status, kw, created, batch,"
                " source, address) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (lead["company"], lead["phone"], lead["email"], lead["website"], lead["city"], lead["country"],
                 lead["score"], "new", lead["kw"], time.time(), batch,
                 lead.get("source", "web"), lead.get("address", "")),
            )
            con.commit()
            return dict(lead, id=cur.lastrowid, status="new", batch=batch)
        except sqlite3.IntegrityError:
            return None
        finally:
            con.close()


def known_hosts():
    """Sites already scanned in earlier runs, so a new run does not fetch them again."""
    with _db_lock:
        con = db()
        rows = {r[0] for r in con.execute("SELECT DISTINCT website FROM leads")}
        con.close()
    return rows


def known_phones():
    """Numbers saved by earlier searches. A new search skips them, so its results are really new."""
    with _db_lock:
        con = db()
        rows = {r[0] for r in con.execute("SELECT DISTINCT phone FROM leads")}
        con.close()
    return rows


def create_batch(params):
    """Every search is its own batch, so its results are listed separately from older searches."""
    name = time.strftime("%Y-%m-%d %H:%M") + " | " + ", ".join(params.get("countries", []))
    with _db_lock:
        con = db()
        cur = con.execute("INSERT INTO batches (name, created, params) VALUES (?,?,?)",
                          (name, time.time(), json.dumps(params, ensure_ascii=False)))
        con.commit()
        bid = cur.lastrowid
        con.close()
    return bid


def set_batch_scanned(batch, scanned):
    with _db_lock:
        con = db()
        con.execute("UPDATE batches SET scanned=? WHERE id=?", (scanned, batch))
        con.commit()
        con.close()


def mark_contacted(lead_id):
    with _db_lock:
        con = db()
        con.execute("UPDATE leads SET status='contacted' WHERE id=? AND status='new'", (lead_id,))
        con.commit()
        con.close()


def log_wa(lead_id, phone, ok, note):
    with _db_lock:
        con = db()
        con.execute("INSERT INTO wa_log (lead_id, phone, ok, note, ts) VALUES (?,?,?,?,?)",
                    (lead_id, phone, 1 if ok else 0, note, time.time()))
        con.commit()
        con.close()


def log_email(lead_id, email, ok, note):
    with _db_lock:
        con = db()
        con.execute("INSERT INTO email_log (lead_id, email, ok, note, ts) VALUES (?,?,?,?,?)",
                    (lead_id, email, 1 if ok else 0, note, time.time()))
        con.commit()
        con.close()


def emails_sent_today():
    midnight = time.mktime(time.localtime()[:3] + (0, 0, 0, 0, 0, -1))
    with _db_lock:
        con = db()
        n = con.execute("SELECT COUNT(*) FROM email_log WHERE ok=1 AND ts>=?", (midnight,)).fetchone()[0]
        con.close()
    return n


def sent_today():
    midnight = time.mktime(time.localtime()[:3] + (0, 0, 0, 0, 0, -1))
    with _db_lock:
        con = db()
        n = con.execute("SELECT COUNT(*) FROM wa_log WHERE ok=1 AND ts>=?", (midnight,)).fetchone()[0]
        con.close()
    return n


# ----------------------------------------------------------------- search
class Searcher:
    """Yields (url, title) for one query. Free by default (DuckDuckGo); keys switch to paid APIs."""

    def __init__(self):
        self.g_key = os.environ.get("GOOGLE_API_KEY")
        self.g_cx = os.environ.get("GOOGLE_CX")
        self.serp_key = os.environ.get("SERPAPI_KEY")

    def results(self, query, country, lang):
        gl = country.lower()
        if self.serp_key:
            yield from self._serpapi(query, gl, lang)
        elif self.g_key and self.g_cx:
            yield from self._google(query, gl, lang)
        else:  # free default: no key needed
            yield from self._ddg(query, country, lang)

    def maps_engine(self):
        if self.g_key:
            return "google_places"
        if self.serp_key:
            return "serpapi_google_maps"
        return "duckduckgo_maps"

    def places(self, query, code, lang):
        """Yields places as dicts: name, phone, website, address. Phone numbers come straight from the map listing."""
        if self.g_key:
            yield from self._places_google(query, code, lang)
        elif self.serp_key:
            yield from self._places_serp(query, lang)
        else:
            yield from self._places_ddg(query)

    def _places_google(self, query, code, lang):  # Places API (New) Text Search, needs billing enabled on the key
        token, pages = None, 0
        while pages < 3:
            body = {"textQuery": query, "languageCode": "ar" if lang == "ar" else "en", "regionCode": code, "pageSize": 20}
            if token:
                body["pageToken"] = token
            try:
                r = requests.post("https://places.googleapis.com/v1/places:searchText", json=body, timeout=TIMEOUT, headers={
                    "X-Goog-Api-Key": self.g_key,
                    "X-Goog-FieldMask": "places.displayName,places.formattedAddress,places.internationalPhoneNumber,"
                                        "places.nationalPhoneNumber,places.websiteUri,nextPageToken"})
            except requests.RequestException:
                return
            if r.status_code != 200:
                return
            data = r.json()
            for pl in data.get("places", []):
                yield {"name": (pl.get("displayName") or {}).get("text", ""),
                       "phone": pl.get("internationalPhoneNumber") or pl.get("nationalPhoneNumber") or "",
                       "website": pl.get("websiteUri", ""), "address": pl.get("formattedAddress", "")}
            token = data.get("nextPageToken")
            pages += 1
            if not token:
                return
            time.sleep(1.5)

    def _places_serp(self, query, lang):
        for start in range(0, 100, 20):
            params = {"engine": "google_maps", "q": query, "type": "search", "hl": "ar" if lang == "ar" else "en",
                      "start": start, "api_key": self.serp_key}
            try:
                r = requests.get("https://serpapi.com/search.json", params=params, timeout=TIMEOUT)
            except requests.RequestException:
                return
            items = r.json().get("local_results", []) if r.status_code == 200 else []
            if not items:
                return
            for it in items:
                yield {"name": it.get("title", ""), "phone": it.get("phone", ""), "website": it.get("website", ""),
                       "address": it.get("address", "")}

    def _places_ddg(self, query):  # free, no key: DuckDuckGo's map search (not Google Maps data)
        try:
            from ddgs import DDGS
        except ImportError:
            from duckduckgo_search import DDGS
        time.sleep(2)
        try:
            items = DDGS().maps(query, max_results=50)
        except Exception:
            time.sleep(8)
            return
        for it in items or []:
            yield {"name": it.get("title", ""), "phone": it.get("phone", ""), "website": it.get("url", ""),
                   "address": it.get("address", "")}

    def _ddg(self, query, code, lang):
        try:
            from ddgs import DDGS
        except ImportError:
            from duckduckgo_search import DDGS
        gulf = {"SA", "AE", "KW", "QA", "BH", "OM"}
        region = ("xa-ar" if lang == "ar" else "xa-en") if code in gulf else "wt-wt"
        for page in (1, 2, 3):  # a few result pages per query
            time.sleep(2)  # stay slow, DuckDuckGo rate-limits fast clients
            try:
                try:
                    items = DDGS().text(query, region=region, max_results=30, page=page)
                except TypeError:  # older ddgs without the page argument
                    items = DDGS().text(query, region=region, max_results=30) if page == 1 else []
            except Exception:
                time.sleep(8)  # rate limited: give up on this query, the next one retries
                return
            if not items:
                return
            for it in items:
                yield it.get("href"), it.get("title", "")

    def _google(self, query, gl, lang):
        start = 1
        while start <= 91:  # the API serves at most 100 results per query
            params = {"key": self.g_key, "cx": self.g_cx, "q": query, "gl": gl, "num": 10, "start": start}
            if lang == "ar":
                params["lr"] = "lang_ar"
            r = requests.get("https://www.googleapis.com/customsearch/v1", params=params, timeout=TIMEOUT)
            if r.status_code != 200:
                return
            items = r.json().get("items", [])
            if not items:
                return
            for it in items:
                yield it.get("link"), it.get("title", "")
            start += 10

    def _serpapi(self, query, gl, lang):
        start = 0
        while start < 200:
            params = {"engine": "google", "q": query, "gl": gl, "hl": "ar" if lang == "ar" else "en",
                      "num": 10, "start": start, "api_key": self.serp_key}
            r = requests.get("https://serpapi.com/search.json", params=params, timeout=TIMEOUT)
            if r.status_code != 200:
                return
            items = r.json().get("organic_results", [])
            if not items:
                return
            for it in items:
                yield it.get("link"), it.get("title", "")
            start += 10


def expand_queries(keywords, codes, lang, widen=True, mods=None):
    """modifier x keyword x country x city. Each combination is a fresh query, so the hunt keeps going
    until the target is reached. The user's own keywords come first, related services after them."""
    kws = list(keywords) + ([s for s in SERVICES if s not in keywords] if widen else [])
    for mod in (MODIFIERS if mods is None else mods):
        for kw in kws:
            for code in codes:
                ar, en, cities = COUNTRIES.get(code, (code, code, [code]))
                for city in cities:
                    if lang in ("ar", "both"):
                        yield kw, code, "ar", " ".join(x for x in (kw, city, ar, mod) if x)
                    if lang in ("en", "both"):
                        yield kw, code, "en", " ".join(x for x in (kw, city, en, mod) if x)


# ----------------------------------------------------------------- extraction
_robots, _last_hit = {}, {}
_net_lock = threading.Lock()


def allowed(url):
    host = urllib.parse.urlparse(url)
    base = f"{host.scheme}://{host.netloc}"
    with _net_lock:
        rp = _robots.get(base)
    if rp is None:
        rp = urllib.robotparser.RobotFileParser()
        try:
            resp = requests.get(base + "/robots.txt", headers={"User-Agent": UA}, timeout=6)
            rp.parse(resp.text.splitlines() if resp.status_code == 200 else [])
        except requests.RequestException:
            rp.parse([])
        with _net_lock:
            _robots[base] = rp
    return rp.can_fetch(UA, url)


def polite_get(url):
    host = urllib.parse.urlparse(url).netloc
    with _net_lock:
        wait = _last_hit.get(host, 0) + PER_DOMAIN_DELAY - time.time()
        _last_hit[host] = time.time() + max(wait, 0)
    if wait > 0:
        time.sleep(wait)
    if not allowed(url):
        return None
    try:
        r = requests.get(url, headers={"User-Agent": UA, "Accept-Language": "ar,en;q=0.8"}, timeout=TIMEOUT)
        if r.status_code == 200 and "text/html" in r.headers.get("content-type", ""):
            r.encoding = r.apparent_encoding or r.encoding
            return r.text
    except requests.RequestException:
        pass
    return None


def normalize_phone(raw, region):
    if phonenumbers:
        try:
            num = phonenumbers.parse(raw, region)
            if phonenumbers.is_valid_number(num):
                return (phonenumbers.format_number(num, phonenumbers.PhoneNumberFormat.INTERNATIONAL),
                        phonenumbers.number_type(num) == phonenumbers.PhoneNumberType.MOBILE)
        except phonenumbers.NumberParseException:
            pass
        return None, False
    digits = re.sub(r"\D", "", raw)
    return ("+" + digits, False) if 9 <= len(digits) <= 14 else (None, False)


def extract(html, url, region, cities):
    soup = BeautifulSoup(html, "html.parser")
    strong, weak, wa = [], [], False  # strong = tel:/WhatsApp links, weak = numbers found in plain text
    for a in soup.find_all("a", href=True):
        h = a["href"]
        if h.startswith("tel:"):
            strong.append(urllib.parse.unquote(h[4:]))
        elif "wa.me/" in h or "api.whatsapp.com" in h:
            wa = True
            m = re.search(r"(\d{8,15})", h)
            if m:
                strong.append("+" + m.group(1))
    text = soup.get_text(" ", strip=True)
    weak = PHONE_RE.findall(text)
    phones = []  # (number, is_mobile, is_strong)
    for raw, is_strong in [(p, True) for p in strong] + [(p, False) for p in weak]:
        n, mob = normalize_phone(raw, region)
        if n and n not in [p[0] for p in phones]:
            phones.append((n, mob, is_strong))
    emails = [e for e in set(EMAIL_RE.findall(html)) if not any(j in e.lower() for j in JUNK_MAIL)]
    emails += [a["href"][7:].split("?")[0] for a in soup.find_all("a", href=True) if a["href"].startswith("mailto:")]
    emails = list(dict.fromkeys(e.strip() for e in emails if e.strip()))
    name = ""
    og = soup.find("meta", property="og:site_name")
    if og and og.get("content"):
        name = og["content"]
    elif soup.title and soup.title.string:
        name = re.split(r"\s[|\-–—]\s", soup.title.string.strip())[0]
    city = next((c for c in cities if c in text), "")
    return {"phones": phones, "emails": emails, "name": name.strip()[:80], "city": city, "wa": wa, "soup": soup}


def contact_pages(soup, base_url):
    out = []
    for a in soup.find_all("a", href=True):
        label = (a.get_text(" ", strip=True) + " " + a["href"]).lower()
        if any(h in label for h in CONTACT_HINTS):
            link = urllib.parse.urljoin(base_url, a["href"])
            if urllib.parse.urlparse(link).netloc == urllib.parse.urlparse(base_url).netloc and link not in out:
                out.append(link)
    return out[:2]


def score_lead(is_mobile, email, wa, city):
    s = 35 + (25 if is_mobile else 10) + (18 if email else 0) + (14 if wa else 0) + (8 if city else 0)
    return min(s, 99)


def pick_phones(phones):
    """Keep the most trustworthy numbers of a site. A page with many loose numbers is a directory,
    so its plain-text numbers are ignored and only tel:/WhatsApp links count."""
    weak = [p for p in phones if not p[2]]
    pool = [p for p in phones if p[2]] + (weak if len(weak) <= 5 else [])
    pool.sort(key=lambda p: (not p[2], not p[1]))  # tel/WhatsApp links first, then mobiles
    return pool[:MAX_PHONES_PER_SITE]


def process_place(pl, code, kw, cities):
    """A map listing already has the phone. The website, when there is one, is only visited for an email address."""
    region = code if len(code) == 2 and code.isalpha() else None
    phone, mobile = normalize_phone(pl.get("phone") or "", region) if pl.get("phone") else (None, False)
    email, wa = "", False
    site = pl.get("website") or ""
    host = urllib.parse.urlparse(site).netloc.lower().replace("www.", "") if site else ""
    if host and not any(host.endswith(d) for d in SKIP_DOMAINS):
        html = polite_get(site)
        if html:
            data = extract(html, site, region, cities)
            email, wa = (data["emails"][0] if data["emails"] else ""), data["wa"]
            if not phone and data["phones"]:
                phone, mobile = pick_phones(data["phones"])[0][:2]
    if not phone:
        return []
    addr = pl.get("address", "")
    city = next((c for c in cities if c in addr), "")
    return [{"company": (pl.get("name") or host or phone)[:80], "phone": phone, "email": email, "website": host,
             "city": city, "country": code, "kw": kw, "score": score_lead(mobile, email, wa, city),
             "source": "maps", "address": addr[:200]}]


def process_site(url, title, code, kw, cities):
    """Returns a list of leads (one per phone number found on the site)."""
    html = polite_get(url)
    if not html:
        return []
    region = code if len(code) == 2 and code.isalpha() else None
    data = extract(html, url, region, cities)
    if not data["phones"]:
        for link in contact_pages(data["soup"], url):
            sub = polite_get(link)
            if sub:
                more = extract(sub, link, region, cities)
                data["phones"] += [p for p in more["phones"] if p[0] not in [q[0] for q in data["phones"]]]
                data["emails"] += more["emails"]
                data["city"] = data["city"] or more["city"]
                data["wa"] = data["wa"] or more["wa"]
            if data["phones"]:
                break
    chosen = pick_phones(data["phones"])
    email = data["emails"][0] if data["emails"] else ""
    host = urllib.parse.urlparse(url).netloc.replace("www.", "")
    company = data["name"] or title[:80] or host
    return [{
        "company": company, "phone": phone, "email": email, "website": host, "city": data["city"],
        "country": code, "kw": kw, "score": score_lead(mob, email, data["wa"], data["city"]),
        "source": "web", "address": "",
    } for phone, mob, _ in chosen]


# ----------------------------------------------------------------- jobs
JOBS = {}


class Job:
    def __init__(self, params):
        self.id = uuid.uuid4().hex[:10]
        self.p = params
        self.target = max(1, int(params.get("target", 1000)))   # numbers wanted
        self.cap = self.target * SITE_CAP_FACTOR                 # sites to scan before giving up
        self.status = "running"
        self.scanned = 0
        self.found = 0
        self.leads, self.log = [], []
        self.stop = threading.Event()
        self.lock = threading.Lock()
        self.batch = 0
        self.known_phones = set()

    def say(self, msg):
        with self.lock:
            self.log.append(msg)

    def finished(self):
        return self.stop.is_set() or self.found >= self.target or self.scanned >= self.cap

    def run(self):
        p = self.p
        for code, name in (p.get("custom") or {}).items():  # countries typed in the dashboard
            COUNTRIES.setdefault(code, (name, name, [name]))
        searcher = Searcher()
        skip = p.get("skip_known", True)
        seen = known_hosts() if skip else set()
        self.known_phones = known_phones() if skip else set()
        sources = p.get("sources") or ["web"]
        seen_places = set()
        try:
            with ThreadPoolExecutor(max_workers=WORKERS) as pool:
                pending = []
                if "maps" in sources:
                    self.say(f"maps source: {searcher.maps_engine()}")
                    for kw, code, lang, query in expand_queries(p["keywords"], p["countries"], p["lang"],
                                                                p.get("widen", True), mods=[""]):
                        if self.finished():
                            break
                        self.say(f"maps: {query}")
                        cities = COUNTRIES.get(code, ("", "", []))[2]
                        for pl in searcher.places(query, code, lang):
                            if self.finished():
                                break
                            key = ((pl.get("name") or "").strip().lower(), (pl.get("address") or "").strip().lower())
                            if key in seen_places or not (pl.get("phone") or pl.get("website")):
                                continue
                            seen_places.add(key)
                            pending.append(pool.submit(process_place, pl, code, kw, cities))
                            self.scanned += 1
                            self._drain(pending)
                        self._drain(pending)
                if "web" in sources:
                    for kw, code, lang, query in expand_queries(p["keywords"], p["countries"], p["lang"],
                                                                p.get("widen", True)):
                        if self.finished():
                            break
                        self.say(f"query: {query}")
                        cities = COUNTRIES.get(code, ("", "", []))[2]
                        pages = 0
                        for link, title in searcher.results(query, code, lang):
                            if self.finished():
                                break
                            if not link:
                                continue
                            host = urllib.parse.urlparse(link).netloc.lower().replace("www.", "")
                            if host in seen or any(host.endswith(d) for d in SKIP_DOMAINS):
                                continue
                            seen.add(host)
                            pending.append(pool.submit(process_site, link, title, code, kw, cities))
                            self.scanned += 1
                            pages += 1
                            if not p.get("unlimited_pages", True) and pages >= 30:
                                break
                            self._drain(pending)
                        self._drain(pending)
                self._drain(pending, wait=True)
            if self.stop.is_set():
                self.status = "stopped"
            else:
                self.status = "done"
                if self.found < self.target:
                    self.say(f"all queries used: {self.found} numbers found")
        except Exception as exc:  # keep the job readable instead of dying silently
            self.say(f"error: {exc}")
            self.status = "error"
        finally:
            set_batch_scanned(self.batch, self.scanned)

    def _drain(self, pending, wait=False):
        for f in list(pending):
            if wait or f.done():
                pending.remove(f)
                try:
                    batch = f.result()
                except Exception:
                    batch = []
                for lead in batch:
                    if lead["phone"] in self.known_phones:
                        continue
                    row = save_lead(lead, self.batch)
                    if row:
                        self.known_phones.add(row["phone"])
                        with self.lock:
                            self.leads.append(row)
                            self.found += 1
                        self.say(f"found {row['phone']} - {row['company']}")


# ----------------------------------------------------------------- server
def create_app():
    from flask import Flask, jsonify, request, send_file, send_from_directory, Response
    from wa_sender import WaSender, MIN_DELAY_FLOOR as WA_MIN_DELAY
    import email_sender
    from email_sender import EmailSender

    app = Flask(__name__)

    @app.get("/")
    def index():
        return send_from_directory(HERE, "index.html")

    @app.get("/api/health")
    def health():
        return jsonify(ok=True, maps=Searcher().maps_engine())

    @app.post("/api/jobs")
    def start_job():
        body = request.get_json(force=True)
        params = {
            "keywords": [k for k in body.get("keywords", []) if k.strip()],
            "countries": body.get("countries", ["SA", "AE"]),
            "custom": body.get("custom", {}),
            "lang": body.get("lang", "ar"),
            "target": int(body.get("target", body.get("max_sites", 1000))),
            "widen": bool(body.get("widen", True)),
            "skip_known": bool(body.get("skip_known", True)),
            "sources": [x for x in body.get("sources", ["web"]) if x in ("web", "maps")] or ["web"],
            "unlimited_pages": bool(body.get("unlimited_pages", True)),
        }
        job = Job(params)
        job.batch = create_batch(params)
        JOBS[job.id] = job
        threading.Thread(target=job.run, daemon=True).start()
        return jsonify(id=job.id, batch=job.batch)

    @app.get("/api/jobs/<job_id>")
    def job_state(job_id):
        job = JOBS.get(job_id)
        if not job:
            return jsonify(error="not found"), 404
        since = int(request.args.get("since", 0))
        with job.lock:
            new = job.leads[since:]
            logs, job.log = job.log[-6:], []
        return jsonify(status=job.status, scanned=job.scanned, found=job.found, target=job.target,
                       batch=job.batch, leads=new, log=logs, next=since + len(new))

    @app.post("/api/jobs/<job_id>/stop")
    def stop_job(job_id):
        job = JOBS.get(job_id)
        if job:
            job.stop.set()
        return jsonify(ok=True)

    @app.get("/api/leads")
    def leads():
        batch = request.args.get("batch", "all")
        con = db()
        if batch == "all":
            rows = [dict(r) for r in con.execute("SELECT * FROM leads ORDER BY id DESC")]
        else:
            rows = [dict(r) for r in con.execute("SELECT * FROM leads WHERE batch=? ORDER BY id DESC", (int(batch),))]
        con.close()
        return jsonify(rows)

    @app.get("/api/batches")
    def batches():
        con = db()
        rows = [dict(r) for r in con.execute(
            "SELECT b.id, b.name, b.created, b.scanned, (SELECT COUNT(*) FROM leads l WHERE l.batch=b.id) AS n"
            " FROM batches b ORDER BY b.id DESC")]
        old = con.execute("SELECT COUNT(*) FROM leads WHERE batch=0").fetchone()[0]
        con.close()
        if old:  # leads saved before searches were split into batches
            rows.append({"id": 0, "name": "older", "created": 0, "scanned": 0, "n": old})
        return jsonify(rows)

    @app.delete("/api/batches/<int:batch_id>")
    def delete_batch(batch_id):
        with _db_lock:
            con = db()
            con.execute("DELETE FROM leads WHERE batch=?", (batch_id,))
            con.execute("DELETE FROM batches WHERE id=?", (batch_id,))
            con.commit()
            con.close()
        return jsonify(ok=True)

    wa = WaSender(os.path.join(HERE, "wa_profile"), mark_contacted, log_wa, sent_today)
    mailer = EmailSender(mark_contacted, log_email, emails_sent_today)

    def num(body, key, default, lo, hi):
        try:
            return min(hi, max(lo, float(body.get(key, default))))
        except (TypeError, ValueError):
            return default

    def load_leads(ids):
        con = db()
        marks = ",".join("?" * len(ids))
        rows = {r["id"]: dict(r) for r in con.execute(f"SELECT * FROM leads WHERE id IN ({marks})", ids)}
        con.close()
        return rows

    # ---- WhatsApp: connect the account first, then send
    @app.post("/api/wa/connect")
    def wa_connect():
        wa.connect()
        return jsonify(ok=True)

    @app.post("/api/wa/disconnect")
    def wa_disconnect():
        wa.disconnect()
        return jsonify(ok=True)

    @app.post("/api/wa/logout")
    def wa_logout():
        wa.logout()
        return jsonify(ok=True)

    @app.post("/api/wa/start")
    def wa_start():
        b = request.get_json(force=True)
        ids = [int(i) for i in b.get("ids", [])]
        msg = (b.get("message") or "").strip()
        if not ids or not msg:
            return jsonify(error="ids and message are required"), 400
        rows = load_leads(ids)
        items, seen_phones = [], set()
        for i in ids:
            r = rows.get(i)
            if not r or r["status"] == "optout":
                continue
            phone = re.sub(r"\D", "", r["phone"] or "")
            if len(phone) < 8 or phone in seen_phones:
                continue
            seen_phones.add(phone)
            text = msg.replace("{company}", r["company"] or "").replace("{city}", r["city"] or "")
            items.append({"id": i, "phone": phone, "text": text})
        if not items:
            return jsonify(error="no valid recipients"), 400
        mn = num(b, "min_delay", 20, WA_MIN_DELAY, 600)
        cfg = {"min_delay": mn, "max_delay": max(mn, num(b, "max_delay", 45, WA_MIN_DELAY, 900)),
               "batch_size": int(num(b, "batch_size", 30, 0, 200)), "batch_pause": num(b, "batch_pause", 5, 0, 60),
               "daily_cap": int(num(b, "daily_cap", 150, 1, 1000))}
        res = wa.start(items, cfg)
        if res == "not_connected":
            return jsonify(error="not_connected"), 409
        if res == "busy":
            return jsonify(error="busy"), 409
        return jsonify(ok=True, total=len(items))

    @app.get("/api/wa/state")
    def wa_state():
        return jsonify(wa.snapshot(int(request.args.get("since", 0))))

    @app.post("/api/wa/stop")
    def wa_stop():
        wa.halt()
        return jsonify(ok=True)

    # ---- Email (SMTP)
    @app.get("/api/email/settings")
    def email_settings():
        return jsonify(settings=email_sender.public_settings(), presets=email_sender.PRESETS)

    @app.post("/api/email/settings")
    def email_settings_save():
        email_sender.save_settings(request.get_json(force=True))
        return jsonify(ok=True, settings=email_sender.public_settings())

    @app.post("/api/email/test")
    def email_test():
        to = (request.get_json(force=True).get("to") or "").strip()
        if "@" not in to:
            return jsonify(error="enter an address"), 400
        try:
            email_sender.send_test(to)
        except smtplib.SMTPAuthenticationError:
            return jsonify(error="Login failed. For Gmail use an App Password."), 400
        except Exception as exc:
            return jsonify(error=str(exc)[:200]), 400
        return jsonify(ok=True)

    @app.post("/api/email/start")
    def email_start():
        b = request.get_json(force=True)
        ids = [int(i) for i in b.get("ids", [])]
        body, subject = (b.get("body") or "").strip(), (b.get("subject") or "").strip()
        if not ids or not body or not subject:
            return jsonify(error="ids, subject and body are required"), 400
        st = email_sender.load_settings()
        if not (st.get("host") and st.get("user") and st.get("password")):
            return jsonify(error="smtp_not_set"), 409
        rows = load_leads(ids)
        con = db()
        done = {r[0] for r in con.execute("SELECT DISTINCT email FROM email_log WHERE ok=1")}
        con.close()
        skip_done = bool(b.get("skip_sent", True))
        items, seen_mail = [], set()
        for i in ids:
            r = rows.get(i)
            em = ((r or {}).get("email") or "").strip().lower()
            if not r or r["status"] == "optout" or "@" not in em or em in seen_mail or (skip_done and em in done):
                continue
            seen_mail.add(em)
            text = body.replace("{company}", r["company"] or "").replace("{city}", r["city"] or "")
            items.append({"id": i, "email": em, "body": text})
        if not items:
            return jsonify(error="no valid recipients"), 400
        mn = num(b, "min_delay", 20, email_sender.MIN_DELAY_FLOOR, 600)
        cfg = {"min_delay": mn, "max_delay": max(mn, num(b, "max_delay", 60, email_sender.MIN_DELAY_FLOOR, 900)),
               "batch_size": int(num(b, "batch_size", 30, 0, 200)), "batch_pause": num(b, "batch_pause", 5, 0, 60),
               "daily_cap": int(num(b, "daily_cap", 100, 1, 2000))}
        if not mailer.start(items, subject, cfg):
            return jsonify(error="busy"), 409
        return jsonify(ok=True, total=len(items))

    @app.get("/api/email/state")
    def email_state():
        return jsonify(mailer.snapshot(int(request.args.get("since", 0))))

    @app.post("/api/email/stop")
    def email_stop():
        mailer.halt()
        return jsonify(ok=True)

    # ---- Excel export
    @app.post("/api/export.xlsx")
    def export_xlsx():
        try:
            from openpyxl import Workbook
            from openpyxl.styles import Alignment, Font, PatternFill
            from openpyxl.utils import get_column_letter
        except ImportError:
            return jsonify(error="openpyxl is not installed. Run: pip install openpyxl"), 500
        b = request.get_json(force=True) if request.data else {}
        ids = [int(i) for i in b.get("ids", [])] if b.get("ids") else None
        con = db()
        if ids:
            marks = ",".join("?" * len(ids))
            rows = con.execute(f"SELECT * FROM leads WHERE id IN ({marks}) ORDER BY id DESC", ids).fetchall()
        elif b.get("batch") not in (None, "all"):
            rows = con.execute("SELECT * FROM leads WHERE batch=? ORDER BY id DESC", (int(b["batch"]),)).fetchall()
        else:
            rows = con.execute("SELECT * FROM leads ORDER BY id DESC").fetchall()
        bnames = {r["id"]: r["name"] for r in con.execute("SELECT id, name FROM batches")}
        con.close()
        ar = (b.get("lang") == "ar")
        head = (["الشركة", "الهاتف", "الإيميل", "الموقع", "المدينة", "الدولة", "التقييم", "الحالة", "المصدر", "العنوان",
                 "كلمة البحث", "الدفعة", "التاريخ"] if ar else
                ["Company", "Phone", "Email", "Website", "City", "Country", "Score", "Status", "Source", "Address",
                 "Keyword", "Batch", "Date"])
        wb = Workbook()
        ws = wb.active
        ws.title = "Leads"
        ws.sheet_view.rightToLeft = ar
        ws.append(head)
        for c in ws[1]:
            c.font = Font(bold=True, color="FFFFFF")
            c.fill = PatternFill("solid", fgColor="2867D5")
            c.alignment = Alignment(horizontal="center", vertical="center")
        for r in rows:
            ts = time.strftime("%Y-%m-%d %H:%M", time.localtime(r["created"])) if r["created"] else ""
            ws.append([r["company"], r["phone"], r["email"], r["website"], r["city"], r["country"], r["score"],
                       r["status"], r["source"] or "web", r["address"] or "", r["kw"],
                       bnames.get(r["batch"], ""), ts])
        for i, w in enumerate((30, 20, 28, 26, 16, 10, 9, 13, 9, 36, 20, 28, 17), start=1):
            ws.column_dimensions[get_column_letter(i)].width = w
        ws.freeze_panes = "A2"
        ws.auto_filter.ref = ws.dimensions
        buf = io.BytesIO()
        wb.save(buf)
        buf.seek(0)
        return send_file(buf, as_attachment=True, download_name="mirage-leads-%s.xlsx" % time.strftime("%Y%m%d-%H%M"),
                         mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

    # ---- logo: served from the folder; downloaded once from the Mirage site if missing
    @app.get("/logo.png")
    def logo():
        path = os.path.join(HERE, "logo.png")
        if not os.path.exists(path):
            try:
                r = requests.get("https://www.mirageemarketing.com/logo.png", timeout=8)
                if r.status_code == 200 and r.content[:4] == b"\x89PNG":
                    with open(path, "wb") as f:
                        f.write(r.content)
            except requests.RequestException:
                pass
        if os.path.exists(path):
            return send_from_directory(HERE, "logo.png")
        return Response(status=404)

    @app.patch("/api/leads/<int:lead_id>")
    def patch_lead(lead_id):
        status = request.get_json(force=True).get("status")
        if status not in STATUSES:
            return jsonify(error="bad status"), 400
        with _db_lock:
            con = db()
            con.execute("UPDATE leads SET status=? WHERE id=?", (status, lead_id))
            con.commit()
            con.close()
        return jsonify(ok=True)

    @app.post("/api/leads/bulk")
    def bulk_status():
        body = request.get_json(force=True)
        status, ids = body.get("status"), [int(i) for i in body.get("ids", [])]
        if status not in STATUSES or not ids:
            return jsonify(error="bad request"), 400
        with _db_lock:
            con = db()
            con.executemany("UPDATE leads SET status=? WHERE id=?", [(status, i) for i in ids])
            con.commit()
            con.close()
        return jsonify(ok=True, n=len(ids))

    @app.get("/api/export.csv")
    def export_csv():
        con = db()
        rows = con.execute("SELECT company,phone,email,website,city,country,score,status FROM leads").fetchall()
        con.close()
        out = ["﻿company,phone,email,website,city,country,score,status"]
        for r in rows:
            out.append(",".join('"' + str(v if v is not None else "").replace('"', '""') + '"' for v in tuple(r)))
        return Response("\n".join(out), mimetype="text/csv",
                        headers={"Content-Disposition": "attachment; filename=mirage-leads.csv"})

    return app


# ----------------------------------------------------------------- cli
def cli():
    ap = argparse.ArgumentParser(description="Mirage Leads Hunter")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("serve")
    s.add_argument("--host", default="127.0.0.1")
    s.add_argument("--port", type=int, default=5000)
    h = sub.add_parser("hunt")
    h.add_argument("--keywords", nargs="+", required=True)
    h.add_argument("--countries", nargs="+", default=["SA", "AE"])
    h.add_argument("--lang", default="ar", choices=["ar", "en", "both"])
    h.add_argument("--target", type=int, default=1000, help="how many phone numbers to collect")
    h.add_argument("--out", default="leads.csv")
    args = ap.parse_args()

    if args.cmd == "serve":
        create_app().run(host=args.host, port=args.port, threaded=True)
        return
    job = Job({"keywords": args.keywords, "countries": args.countries, "lang": args.lang,
               "target": args.target, "unlimited_pages": True})
    t = threading.Thread(target=job.run, daemon=True)
    t.start()
    try:
        while t.is_alive():
            time.sleep(2)
            print(f"scanned={job.scanned} numbers={job.found}/{job.target}", file=sys.stderr)
    except KeyboardInterrupt:
        job.stop.set()
        t.join()
    with open(args.out, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=["company", "phone", "email", "website", "city", "country", "score", "status"],
                           extrasaction="ignore")
        w.writeheader()
        w.writerows(job.leads)
    print(f"saved {len(job.leads)} numbers to {args.out}")


if __name__ == "__main__":
    cli()

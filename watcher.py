#!/usr/bin/env python3
"""MacBook Pro deal watcher.

Checks every MacBook Pro listed at Plaisio, Kotsovolos, Public and BestPrice, plus
store newsletters in an IMAP mailbox, and sends Telegram alerts on price drops,
restocks, new listings and MacBook Pro newsletters.

  python watcher.py                 one check (what GitHub Actions runs)
  python watcher.py --loop 90       check every 90s forever (e.g. on your Mac)
  python watcher.py --dry-run       print alerts instead of sending them
  python watcher.py --telegram-chat-id   print chat ids that messaged the bot
"""
import argparse
import email
import email.header
import email.utils
import html
import imaplib
import json
import os
import re
import sys
import time
import traceback
import urllib.parse
import urllib.request
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

# ---------------------------------------------------------------- settings --

LOUD_DROP_EUR = 100      # loud alert when a price drops by at least this much...
LOUD_DROP_PCT = 5        # ...or by at least this many percent
QUIET_DROP_EUR = 20      # smaller drops (>= this) still arrive, without sound
BIG_DISCOUNT_PCT = 15    # store shows >= 15% off its own old price -> loud alert
FAILS_BEFORE_ALERT = 3   # consecutive failed runs before "source is broken"
MISSING_RUNS_FOR_RETURN = 3  # gone this many runs, then back -> "back" alert
DAILY_REPORT_HOUR = 9    # Athens time, quiet "still alive" summary
MAX_MESSAGES_PER_RUN = 15

TZ = ZoneInfo("Europe/Athens")
STATE_FILE = Path(__file__).with_name("state.json")
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36")

NOT_A_LAPTOP = re.compile(
    r"\b(case|sleeve|charger|adapter|cable|hub|dock|battery|protector|cover|bag|stand|skin)\b"
    r"|θήκη|φορτιστ|αντάπτορ|καλώδι|μπαταρ|προστατευτ|κάλυμμα|τσάντα|βάση", re.I)

WANTED = re.compile(r"mac\s?book\s+pro\b", re.I)  # "Apple MacBook Pro 14 M5", not "MacBook Neo (A18 Pro)"
MAIL_LOUD = re.compile(r"mac\s?book\s?pro", re.I)
MAIL_QUIET = re.compile(r"\b(apple|mac|black\s?friday|cyber\s?monday)\b|mac\s?book|προσφορ|εκπτώσ|εκπτωσ", re.I)
STORE_SENDERS = ("kotsovolos", "plaisio", "public", "mediamarkt", "bestprice", "skroutz",
                 "istorm", "you.gr", "kaitatzis", "e-shop", "germanos", "apple")

STORE_NAMES = {
    "plaisio": "Πλαίσιο",
    "kotsovolos": "Κωτσόβολος",
    "public": "Public",
    "bestprice": "BestPrice (φθηνότερο κατάστημα)",
    "newsletter": "Newsletters",
}

# ----------------------------------------------------------------- helpers --


def get(url, timeout=30, tries=3):
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "el-GR,el;q=0.9",
    })
    for attempt in range(tries):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read().decode("utf-8", "replace")
        except (OSError, urllib.error.URLError):
            if attempt == tries - 1:
                raise
            time.sleep(3 * (attempt + 1))


def parse_eur(text):
    """'€1.399,99' / '2249.99' / '1.449,00€' -> float."""
    s = re.sub(r"[^\d.,]", "", str(text))
    if not s:
        return None
    if "," in s and "." in s:
        dec = "," if s.rfind(",") > s.rfind(".") else "."
        s = s.replace("." if dec == "," else ",", "").replace(dec, ".")
    elif "," in s:
        s = s.replace(",", ".")
    elif s.count(".") == 1 and len(s.split(".")[1]) == 3:
        s = s.replace(".", "")  # 1.449 = thousands separator
    try:
        return float(s)
    except ValueError:
        return None


def item(name, url, price, old_price=None, in_stock=None, note=""):
    return {"name": " ".join(str(name).split()), "url": url, "price": price,
            "old_price": old_price, "in_stock": in_stock, "note": note}


LD_RE = re.compile(r'<script[^>]*application/ld\+json[^>]*>(.*?)</script>', re.S)


def ld_products(page_html, base_url):
    """All schema.org Products (with a price) found in a page's JSON-LD."""
    found = []

    def walk(o):
        if isinstance(o, list):
            for x in o:
                walk(x)
        elif isinstance(o, dict):
            if o.get("@type") == "Product":
                found.append(o)
            for v in o.values():
                walk(v)

    for m in LD_RE.finditer(page_html):
        try:
            walk(json.loads(m.group(1)))
        except ValueError:
            pass
    out = []
    for p in found:
        offer = p.get("offers") or {}
        if isinstance(offer, list):
            offer = offer[0] if offer else {}
        price = parse_eur(offer.get("price") or offer.get("lowPrice") or "")
        if not price:
            continue
        avail = offer.get("availability") or ""
        in_stock = ("InStock" in avail or "LimitedAvailability" in avail) if avail else None
        url = urllib.parse.urljoin(base_url, p.get("url") or offer.get("url") or "")
        out.append(item(p.get("name", ""), url, price, in_stock=in_stock))
    return out


def is_wanted(name):
    return bool(WANTED.search(name)) and not NOT_A_LAPTOP.search(name)


def canon(url):
    p = urllib.parse.urlsplit(url)
    return f"{p.netloc}{p.path}".lower().rstrip("/")


def eur(x):
    return f"€{x:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")


def esc(s):
    return html.escape(str(s), quote=False)


SECRET_ENV = ("TELEGRAM_BOT_TOKEN", "TELEGRAM_CHAT_ID", "IMAP_USER", "IMAP_PASSWORD")


def redact(text):
    """state.json and the Actions log are public: never let a secret into them."""
    text = str(text)
    for name in SECRET_ENV:
        value = os.environ.get(name)
        if value:
            text = text.replace(value, "***")
    return text


class Browser:
    """Headless Chrome, started only if a source needs it."""

    def __init__(self):
        self._pw = self._browser = None

    def page(self, block=("image", "media", "font")):
        if not self._browser:
            from playwright.sync_api import sync_playwright
            self._pw = sync_playwright().start()
            try:  # GitHub's Ubuntu runners ship Google Chrome
                self._browser = self._pw.chromium.launch(channel="chrome", headless=True)
            except Exception:
                self._browser = self._pw.chromium.launch(headless=True)
        pg = self._browser.new_page(locale="el-GR", user_agent=UA,
                                    viewport={"width": 1366, "height": 900})
        pg.route("**/*", lambda r: r.abort() if r.request.resource_type in block else r.continue_())
        return pg

    def close(self):
        if self._browser:
            self._browser.close()
            self._pw.stop()


MORE_BUTTON = re.compile(r"^\s*(Δες περισσότερα\s*$|Φόρτωση επόμενων)", re.I)


def listing_total(pg):
    """'Είδες 36 από 74 προϊόντα' / 'έχετε δει 13 από 72 προϊόντα' -> 74 / 72."""
    m = re.search(r"από\s+(\d+)\s+προϊόντα", pg.inner_text("body"))
    return int(m.group(1)) if m else None


def load_all(pg, count, total=None, rounds=25):
    """Press 'load more' until count() reaches total or stops growing."""
    last, still = -1, 0
    for _ in range(rounds):
        n = count()
        if total and n >= total:
            break
        still = still + 1 if n == last else 0
        if still >= 2:
            break
        last = n
        pg.evaluate("window.scrollTo(0, document.body.scrollHeight)")
        more = pg.locator("button, a", has_text=MORE_BUTTON)
        if more.count():
            try:  # a JS click is not blocked by cookie banners covering the button
                more.last.evaluate("e => e.click()")
            except Exception:
                pass
        deadline = time.time() + 8
        while time.time() < deadline and count() <= n:
            pg.wait_for_timeout(400)

# ----------------------------------------------------------------- sources --


def src_plaisio(_browser):
    base = "https://www.plaisio.gr/list/pc-perifereiaka/laptops/apple-macbook"
    out, seen = [], set()
    for page in range(1, 20):
        url = base if page == 1 else f"{base}?page={page}"
        batch = [p for p in ld_products(get(url), url) if p["url"] not in seen]
        if not batch:
            break
        seen.update(p["url"] for p in batch)
        out += batch
        time.sleep(1)
    return out


BP_BLOCK = re.compile(r"<div\s+data-id=['\"](\d+)['\"]\s+data-cid=['\"]\d+['\"]\s+data-price=['\"](\d+)['\"]")


def src_bestprice(browser):
    # server-rendered, but Python's HTTP client gets no answer here, so use the browser
    base = "https://www.bestprice.gr/cat/2591/laptops/f/1_9/apple-macbook.html"
    pg = browser.page(block=("image", "media", "font", "script", "stylesheet"))
    try:
        return _bestprice_pages(pg, base)
    finally:
        pg.close()


def _bestprice_pages(pg, base):
    out, seen = [], set()
    for page in range(1, 20):
        pg.goto(base if page == 1 else f"{base}?pg={page}", wait_until="domcontentloaded", timeout=60000)
        h = pg.content()
        blocks = list(BP_BLOCK.finditer(h))
        new = 0
        for i, m in enumerate(blocks):
            if m.group(1) in seen:
                continue
            seen.add(m.group(1))
            end = blocks[i + 1].start() if i + 1 < len(blocks) else m.start() + 10000
            block = h[m.start():end]
            t = re.search(r'class="p__title"><a href="([^"]+)" title="([^"]+)"', block)
            if not t or int(m.group(2)) <= 0:  # 0 = not sold anywhere yet
                continue
            shops = re.search(r'p__merchants">([^<]+)<', block)
            out.append(item(html.unescape(t.group(2)), urllib.parse.urljoin(base, t.group(1)),
                            int(m.group(2)) / 100, in_stock=True,
                            note=shops.group(1).strip() if shops else ""))
            new += 1
        if not new:
            break
        time.sleep(1)
    return out


KOTS_CARDS_JS = """() => [...document.querySelectorAll('a.product-name-link')].map(a => {
  let el = a;
  for (let i = 0; i < 8 && el; i++) {
    el = el.parentElement;
    if (el && /€/.test(el.innerText) && el.innerText.length > 80) break;
  }
  return {name: a.innerText.trim(), url: a.href, card: el ? el.innerText : ''};
})"""
KOTS_OUT = re.compile(r"εξαντλ|μη διαθέσιμ|δεν είναι διαθέσιμ|ενημέρωσέ με|προσωρινά|αναμένεται", re.I)
KOTS_IN = re.compile(r"διαθέσιμ|προπαραγγελ", re.I)


def src_kotsovolos(browser):
    url = "https://www.kotsovolos.gr/computing/laptop-tablet-ipad/notebook-macbook-ultrabook/filters/m/Apple"
    pg = browser.page()
    try:
        pg.goto(url, wait_until="domcontentloaded", timeout=60000)
        pg.wait_for_selector("a.product-name-link", timeout=40000)
        pg.wait_for_timeout(1500)
        load_all(pg, lambda: pg.locator("a.product-name-link").count(), listing_total(pg))
        cards = pg.evaluate(KOTS_CARDS_JS)
    finally:
        pg.close()
    out, seen = [], set()
    for c in cards:
        if c["url"] in seen:
            continue
        seen.add(c["url"])
        card = c["card"]
        # drop "κέρδος €850" (the saving) and instalment lines before reading prices
        priced = re.sub(r"κέρδος\s*€\s?[\d.,]+", " ", card, flags=re.I)
        priced = "\n".join(l for l in priced.split("\n") if not re.search(r"δόσ|/μήνα|μηνιαί", l, re.I))
        prices = [p for p in (parse_eur(x) for x in re.findall(r"€\s?[\d.,]+", priced)) if p]
        if not prices:
            continue
        price = prices[-1]
        old = prices[-2] if len(prices) >= 2 and prices[-2] > price else None
        in_stock = False if KOTS_OUT.search(card) else (True if KOTS_IN.search(card) else None)
        out.append(item(c["name"], c["url"], price, old_price=old, in_stock=in_stock))
    return out


def src_public(browser):
    url = "https://www.public.gr/cat/apple/macbook"
    found = {}

    def collect():  # each 'Δες περισσότερα' replaces the JSON-LD with just the new batch
        for p in ld_products(pg.content(), url):
            found.setdefault(canon(p["url"]), p)
        return len(found)

    pg = browser.page()
    try:
        pg.goto(url, wait_until="domcontentloaded", timeout=60000)
        pg.wait_for_function("""() => [...document.querySelectorAll('script[type="application/ld+json"]')]
                                .some(s => s.textContent.includes('ItemList'))""", timeout=40000)
        load_all(pg, collect, listing_total(pg))
        collect()
    finally:
        pg.close()
    return list(found.values())


SOURCES = {
    "plaisio": src_plaisio,
    "kotsovolos": src_kotsovolos,
    "public": src_public,
    "bestprice": src_bestprice,
}

# -------------------------------------------------------------- newsletters --


def decode(value):
    parts = []
    for text, charset in email.header.decode_header(value or ""):
        parts.append(text.decode(charset or "utf-8", "replace") if isinstance(text, bytes) else text)
    return "".join(parts)


def mail_text(msg):
    """Plain text of an email (including image alt texts) and its MacBook links."""
    texts, links = [], []
    for part in msg.walk():
        ctype = part.get_content_type()
        if ctype not in ("text/plain", "text/html"):
            continue
        payload = part.get_payload(decode=True) or b""
        body = payload.decode(part.get_content_charset() or "utf-8", "replace")
        if ctype == "text/html":
            body = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", body, flags=re.S | re.I)
            for href, inner in re.findall(r'<a\s[^>]*href="([^"]+)"[^>]*>(.*?)</a>', body, re.S | re.I):
                label = " ".join(re.findall(r'alt="([^"]*)"', inner)) + " " + re.sub(r"<[^>]+>", " ", inner)
                if MAIL_LOUD.search(href) or MAIL_LOUD.search(label):
                    links.append(html.unescape(href))
            body = " ".join(re.findall(r'alt="([^"]*)"', body)) + " " + re.sub(r"<[^>]+>", " ", body)
            body = html.unescape(body)
        texts.append(body)
    return " ".join(" ".join(texts).split()), list(dict.fromkeys(links))


def check_newsletters(state, alerts):
    user, password = os.environ.get("IMAP_USER"), os.environ.get("IMAP_PASSWORD")
    if not (user and password):
        return False
    host = os.environ.get("IMAP_HOST") or "imap.gmail.com"
    box = imaplib.IMAP4_SSL(host, timeout=30)
    try:
        box.login(user, password)
        box.select("INBOX", readonly=True)
        status = box.status("INBOX", "(UIDVALIDITY UIDNEXT)")[1][0].decode()
        validity = int(re.search(r"UIDVALIDITY (\d+)", status).group(1))
        uidnext = int(re.search(r"UIDNEXT (\d+)", status).group(1))
        mail = state.setdefault("mail", {})
        if mail.get("uidvalidity") != validity:  # first run: start from now
            state["mail"] = {"uidvalidity": validity, "last_uid": uidnext - 1}
            return True
        last = mail["last_uid"]
        if uidnext - 1 <= last:
            return True
        found = box.uid("search", None, f"UID {last + 1}:*")[1][0].split()
        uids = sorted(int(u) for u in found if int(u) > last)
        for uid in uids[-30:]:
            raw = box.uid("fetch", str(uid), "(BODY.PEEK[])")[1][0][1]
            msg = email.message_from_bytes(raw)
            subject, sender = decode(msg["Subject"]), decode(msg["From"])
            text, links = mail_text(msg)
            from_store = any(s in sender.lower() for s in STORE_SENDERS)
            hit = MAIL_LOUD.search(subject + " " + text)
            if hit:
                a = max(0, hit.start() - len(subject) - 120)
                snippet = text[a:a + 300]
                lines = [f"📧 <b>Newsletter για MacBook Pro</b>", f"<b>{esc(sender)}</b>",
                         f"«{esc(subject)}»", f"…{esc(snippet)}…"]
                lines += [f"👉 {esc(link)}" for link in links[:3]]
                alerts.append(("\n".join(lines), True))
            elif from_store and MAIL_QUIET.search(subject + " " + text):
                alerts.append((f"📧 {esc(sender)}\n«{esc(subject)}»", False))
        mail["last_uid"] = max(uids + [last])
    finally:
        try:
            box.logout()
        except Exception:
            pass
    return True

# --------------------------------------------------------------- comparing --


def compare(state, store, items, alerts):
    products = state.setdefault("products", {})
    prefix = store + "|"
    first_time = not any(k.startswith(prefix) for k in products)
    shop = STORE_NAMES[store]
    seen = set()
    for it in items:
        key = prefix + canon(it["url"])
        if key in seen:
            continue
        seen.add(key)
        old = products.get(key)
        price = it["price"]
        rec = {
            "name": it["name"], "url": it["url"], "price": price,
            "old_price": it["old_price"], "in_stock": it["in_stock"], "missing": 0,
            "low": min(price, old["low"]) if old else price,
            "high": max(price, old["high"]) if old else price,
        }
        products[key] = rec
        off = (it["old_price"] - price) / it["old_price"] * 100 if it["old_price"] else 0
        shown_off = f"{eur(it['old_price'])} → " if it["old_price"] else ""
        extra = f"\n{esc(it['note'])}" if it["note"] else ""
        if old is None:
            if first_time and off < BIG_DISCOUNT_PCT:
                continue
            title = (f"🔥 <b>Έκπτωση −{off:.0f}% (−{eur(it['old_price'] - price)})</b>"
                     if off >= BIG_DISCOUNT_PCT else "🆕 <b>Νέο MacBook στη λίστα</b>")
            alerts.append((f"{title}\n<b>{shop}</b>: {esc(it['name'])}\n"
                           f"{shown_off}<b>{eur(price)}</b>{extra}\n👉 {it['url']}",
                           off >= BIG_DISCOUNT_PCT))
            continue
        drop = old["price"] - price
        pct = drop / old["price"] * 100
        if drop >= QUIET_DROP_EUR:
            loud = drop >= LOUD_DROP_EUR or pct >= LOUD_DROP_PCT
            icon = "🚨" if pct >= 25 else ("🔥" if loud else "📉")
            low_note = " (χαμηλότερη που έχω δει)" if price <= old["low"] else f" (χαμηλότερη: {eur(old['low'])})"
            alerts.append((f"{icon} <b>Πτώση τιμής −{eur(drop)} (−{pct:.0f}%)</b>\n"
                           f"<b>{shop}</b>: {esc(it['name'])}\n"
                           f"{eur(old['price'])} → <b>{eur(price)}</b>{low_note}{extra}\n👉 {it['url']}", loud))
        elif old.get("in_stock") is False and it["in_stock"]:
            alerts.append((f"✅ <b>Ξανά διαθέσιμο</b>\n<b>{shop}</b>: {esc(it['name'])}\n"
                           f"<b>{eur(price)}</b>{extra}\n👉 {it['url']}", True))
        elif old.get("missing", 0) >= MISSING_RUNS_FOR_RETURN:
            alerts.append((f"↩️ <b>Ξαναεμφανίστηκε</b>\n<b>{shop}</b>: {esc(it['name'])}\n"
                           f"<b>{eur(price)}</b>{extra}\n👉 {it['url']}", True))
    for key, rec in products.items():
        if key.startswith(prefix) and key not in seen:
            rec["missing"] = min(rec.get("missing", 0) + 1, MISSING_RUNS_FOR_RETURN)
    return first_time


def source_ok(state, name, alerts):
    health = state.setdefault("health", {})
    if health.get(name, {}).get("fails", 0) >= FAILS_BEFORE_ALERT:
        alerts.append((f"✅ {STORE_NAMES[name]}: δουλεύει ξανά", False))
    health.pop(name, None)


def source_failed(state, name, err, alerts):
    h = state.setdefault("health", {}).setdefault(name, {"fails": 0})
    h["fails"] += 1
    h["error"] = redact(err)[:300]
    print(f"[{name}] FAILED: {h['error']}", file=sys.stderr)
    if h["fails"] == FAILS_BEFORE_ALERT:
        alerts.append((f"⚠️ <b>Δεν μπορώ να διαβάσω: {STORE_NAMES[name]}</b>\n"
                       f"{FAILS_BEFORE_ALERT} φορές στη σειρά. Μέχρι να φτιαχτεί, εκεί δεν βλέπω προσφορές.\n"
                       f"<code>{esc(h['error'])}</code>", True))


def daily_report(state, alerts, force=False):
    now = datetime.now(TZ)
    today = now.date().isoformat()
    if not force and (now.hour < DAILY_REPORT_HOUR or state.get("daily") == today):
        return
    state["daily"] = today
    live = [(k.split("|")[0], p) for k, p in state.get("products", {}).items() if not p.get("missing")]
    counts = {}
    for store, _ in live:
        counts[store] = counts.get(store, 0) + 1
    lines = ["🟢 <b>Το bot δουλεύει</b>",
             " · ".join(f"{STORE_NAMES[s].split(' (')[0]}: {n}" for s, n in sorted(counts.items()))]
    for size in ("14", "16"):
        options = [(p["price"], s, p) for s, p in live
                   if (m := re.search(r"\b(14|16)\b", WANTED.split(p["name"])[-1])) and m.group(1) == size
                   and p.get("in_stock") is not False]
        if options:
            price, s, p = min(options, key=lambda o: o[0])
            lines.append(f"Φθηνότερο MacBook Pro {size}\": <b>{eur(price)}</b> ({STORE_NAMES[s].split(' (')[0]})\n{p['url']}")
    broken = [STORE_NAMES[n] for n, h in state.get("health", {}).items() if h.get("fails", 0) >= FAILS_BEFORE_ALERT]
    if broken:
        lines.append("⚠️ Δεν διαβάζονται: " + ", ".join(broken))
    alerts.append(("\n".join(lines), False))

# ---------------------------------------------------------------- telegram --


def telegram(method, **params):
    token = os.environ["TELEGRAM_BOT_TOKEN"]
    data = urllib.parse.urlencode(params).encode()
    req = urllib.request.Request(f"https://api.telegram.org/bot{token}/{method}", data=data)
    with urllib.request.urlopen(req, timeout=20) as r:
        return json.load(r)


def send(alerts, dry_run):
    if len(alerts) > MAX_MESSAGES_PER_RUN:
        rest = len(alerts) - MAX_MESSAGES_PER_RUN + 1
        loud = any(l for _, l in alerts[MAX_MESSAGES_PER_RUN - 1:])
        alerts = alerts[:MAX_MESSAGES_PER_RUN - 1] + [(f"…και άλλες {rest} ειδοποιήσεις.", loud)]
    can_send = os.environ.get("TELEGRAM_BOT_TOKEN") and os.environ.get("TELEGRAM_CHAT_ID")
    for text, loud in alerts:
        if dry_run or not can_send:
            print(("🔔 " if loud else "🔕 ") + re.sub(r"<[^>]+>", "", text) + "\n")
            continue
        try:
            telegram("sendMessage", chat_id=os.environ["TELEGRAM_CHAT_ID"], text=text[:4000],
                     parse_mode="HTML", disable_notification=str(not loud).lower())
        except Exception as e:
            print(f"telegram send failed: {redact(e)}", file=sys.stderr)
        time.sleep(0.5)

# -------------------------------------------------------------------- main --


def load_state():
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text())
    return {}


def save_state(state):
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=1, sort_keys=True) + "\n")


def run_once(dry_run=False, only=None):
    state = load_state()
    brand_new = not state.get("products")
    alerts, summary = [], {}
    skip = set(os.environ.get("SKIP_SOURCES", "").replace(",", " ").split())
    browser = Browser()
    try:
        for name, fn in SOURCES.items():
            if (only and name not in only) or name in skip:
                continue
            started = time.time()
            try:
                items = [i for i in fn(browser) if is_wanted(i["name"])]
                if not items:
                    raise RuntimeError("βρέθηκαν 0 MacBook Pro (άλλαξε η σελίδα;)")
            except Exception as e:
                source_failed(state, name, f"{type(e).__name__}: {e}", alerts)
                summary[name] = "FAILED"
                continue
            source_ok(state, name, alerts)
            compare(state, name, items, alerts)
            summary[name] = f"{len(items)} MacBook Pros in {time.time() - started:.0f}s"
    finally:
        browser.close()
    if not only or "newsletter" in only:
        try:
            if check_newsletters(state, alerts):
                source_ok(state, "newsletter", alerts)
                summary["newsletter"] = "ok"
        except Exception as e:
            source_failed(state, "newsletter", f"{type(e).__name__}: {e}", alerts)
            summary["newsletter"] = "FAILED"
    daily_report(state, alerts, force=brand_new)
    if brand_new:
        alerts.insert(0, ("🚀 <b>Ξεκίνησα!</b> Από εδώ και πέρα θα σου στέλνω κάθε πτώση τιμής σε MacBook Pro.", True))
    save_state(state)
    send(alerts, dry_run)
    print(json.dumps(summary, ensure_ascii=False))
    return summary


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--loop", type=int, metavar="SECONDS", help="keep checking every SECONDS")
    ap.add_argument("--dry-run", action="store_true", help="print alerts instead of sending them")
    ap.add_argument("--only", nargs="+", choices=[*SOURCES, "newsletter"], help="check only these sources")
    ap.add_argument("--telegram-chat-id", action="store_true", help="print chats that messaged the bot")
    args = ap.parse_args()

    if args.telegram_chat_id:
        for u in telegram("getUpdates").get("result", []):
            chat = (u.get("message") or u.get("channel_post") or {}).get("chat", {})
            if chat:
                print(chat["id"], chat.get("username") or chat.get("title") or chat.get("first_name"))
        return

    telegram_ready = os.environ.get("TELEGRAM_BOT_TOKEN") and os.environ.get("TELEGRAM_CHAT_ID")
    if os.environ.get("GITHUB_ACTIONS") == "true" and not telegram_ready and not args.dry_run:
        # don't record a baseline nobody was told about; the first run with secrets does that
        print("TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID secrets are not set yet: skipping this run.")
        return

    while True:
        try:
            summary = run_once(args.dry_run, args.only)
        except Exception:
            print(redact(traceback.format_exc()), file=sys.stderr)
            if not args.loop:
                sys.exit(1)
        else:
            if not args.loop and summary and all(v == "FAILED" for v in summary.values()):
                sys.exit(1)  # everything broken: let GitHub email you a failed run
        if not args.loop:
            break
        time.sleep(args.loop)


if __name__ == "__main__":
    main()

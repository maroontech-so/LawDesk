from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import socket
import sqlite3
import sys
import threading
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from flask import Flask, jsonify, render_template, request
from flask_cors import CORS
from werkzeug.exceptions import HTTPException

try:
    import fitz

    _HAS_FITZ = True
except ImportError:
    _HAS_FITZ = False

load_dotenv()

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
JSON_DIR = BASE_DIR / "downloads" / "json"
TEMPLATE_DIR = BASE_DIR / "templates"
DB_PATH = DATA_DIR / "eklr.sqlite3"
CONSTITUTION_JSON_PATH = DATA_DIR / "constitution.json"
ACTS_JSON_PATH = DATA_DIR / "acts.json"

for folder in (DATA_DIR, JSON_DIR, TEMPLATE_DIR):
    folder.mkdir(parents=True, exist_ok=True)

HOST = os.getenv("EKLR_HOST", "127.0.0.1")
PORT = int(os.getenv("EKLR_PORT", "5000"))
MAX_RESULTS = max(5, min(int(os.getenv("EKLR_MAX_CANDIDATES", "40")), 80))
FETCH_WORKERS = max(2, min(int(os.getenv("EKLR_FETCH_WORKERS", "6")), 16))

OFFICIAL_HOSTS = {
    "kenyalaw.org",
    "www.kenyalaw.org",
    "new.kenyalaw.org",
    "old.kenyalaw.org",
    "judiciary.go.ke",
    "www.judiciary.go.ke",
    "parliament.go.ke",
    "www.parliament.go.ke",
}

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36 LawDesk/1.0"
)
HTTP_TIMEOUT = (5, 25)
SCHEMA_VERSIONS = {"case": 7, "statute": 17}

MIN_INTERVAL = 1.2
_rate_lock = threading.Lock()
_last_request = [0.0]

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("lawdesk")

if not _HAS_FITZ:
    log.warning("PyMuPDF not installed — PDF fallback disabled")

app = Flask(__name__, template_folder=str(TEMPLATE_DIR))
CORS(app)
app.config["JSON_SORT_KEYS"] = False
app.config["SEND_FILE_MAX_AGE_DEFAULT"] = 86400

local = threading.local()
FETCH_POOL = ThreadPoolExecutor(max_workers=FETCH_WORKERS, thread_name_prefix="fetch")

_inflight: set[str] = set()
_inflight_lock = threading.Lock()


def rate_limit():
    with _rate_lock:
        wait = MIN_INTERVAL - (time.time() - _last_request[0])
        if wait > 0:
            time.sleep(wait)
        _last_request[0] = time.time()


class KenyaLaw:
    BASE = "https://new.kenyalaw.org"
    SEARCH_HTML = "/search/"
    SEARCH_API = "/search/api/documents/"

    def __init__(self):
        self._session = requests.Session()
        self._session.headers.update(
            {
                "User-Agent": USER_AGENT,
                "Accept": "text/html,application/json;q=0.9,*/*;q=0.8",
                "Accept-Language": "en-US,en;q=0.9",
                "Referer": "https://new.kenyalaw.org/",
            }
        )

    def get(self, url, params=None, headers=None, timeout=(5, 25)):
        rate_limit()
        try:
            r = self._session.get(
                url,
                params=params,
                headers=headers,
                timeout=timeout,
                allow_redirects=True,
            )
            r.raise_for_status()
            return r
        except requests.RequestException as exc:
            log.debug("GET %s → %s", url, exc)
            return None

    def search_html(self, q: str, kind: str, limit: int = 20):
        params = {"q": q}
        if kind == "statute":
            params["type"] = "legislation"
            prefix = "/akn/ke/act/"
        else:
            params["type"] = "judgment"
            prefix = "/akn/ke/judgment/"
        r = self.get(self.BASE + self.SEARCH_HTML, params=params, timeout=(3, 8))
        if r is None:
            return [], "EKLR unreachable"
        docs = _parse_html_fragment(r.text)
        docs = [d for d in docs if prefix in d["url"]]
        return docs[:limit], None


KL = KenyaLaw()


def canonical_eklr_url(raw: str) -> str:
    raw = (raw or "").strip()
    if not raw:
        return ""
    if raw.startswith("//"):
        raw = "https:" + raw
    if raw.startswith("/"):
        raw = "https://new.kenyalaw.org" + raw
    elif not raw.startswith(("http://", "https://")):
        raw = "https://new.kenyalaw.org/" + raw.lstrip("/")
    try:
        p = urlparse(raw)
    except ValueError:
        return ""
    host = (p.hostname or "").lower()
    if host not in OFFICIAL_HOSTS:
        return ""
    path = re.sub(r"/+$", "", p.path or "/")
    if "/akn/ke/" not in path:
        return ""
    return f"https://{host}{path}"


def is_case_url(url: str) -> bool:
    return bool(url) and bool(
        re.search(r"/akn/ke/judgment/|/caselaw/cases/view/\d+", url, re.I)
    )


def is_act_url(url: str) -> bool:
    return bool(url) and bool(re.search(r"/akn/ke/act/", url, re.I))


def kind_for_url(url: str, hint=None) -> str:
    if is_case_url(url):
        return "case"
    if is_act_url(url):
        return "statute"
    return hint if hint in ("case", "statute", "constitution") else "case"


def _clean(v) -> str:
    return re.sub(r"\s+", " ", str(v or "")).strip()


def _scan_strings_for_urls(text: str) -> list[str]:
    urls, seen = [], set()
    for m in re.finditer(r'(?:https?://[^\s"\'<>)]+)?/akn/ke/[^\s"\'<>)]+', text or ""):
        u = canonical_eklr_url(m.group(0))
        if u and u not in seen:
            seen.add(u)
            urls.append(u)
    return urls


def _parse_html_fragment(html: str) -> list[dict]:
    if not html or not html.strip():
        return []
    soup = BeautifulSoup(html, "html.parser")
    out, seen = [], set()
    for li in soup.select("li.hit"):
        a = li.select_one("a.h5") or li.select_one("a[href*='/akn/']")
        if not a:
            a = li.find("a", href=True)
        if not a:
            continue
        url = canonical_eklr_url(a.get("href") or "")
        if not url or url in seen:
            continue
        seen.add(url)
        title = _clean(a.get_text(" ", strip=True)) or "Kenya Law document"
        citation = ""
        i_tag = li.find("i")
        if i_tag:
            citation = _clean(i_tag.get_text(" ", strip=True))
        date, court = "", ""
        spans = li.select("span.me-3")
        if spans:
            date = _clean(spans[0].get_text(" ", strip=True))
            if len(spans) > 1:
                court = _clean(spans[1].get_text(" ", strip=True))
        snip_div = li.select_one("div.snippet, p.snippet")
        snippet = _clean(snip_div.get_text(" ", strip=True)) if snip_div else ""
        out.append(
            {
                "url": url,
                "title": title,
                "citation": citation,
                "court": court,
                "date": date,
                "snippet": snippet,
            }
        )
    if out:
        return out
    for a in soup.find_all("a", href=True):
        url = canonical_eklr_url(a.get("href") or "")
        if not url or url in seen:
            continue
        seen.add(url)
        title = _clean(a.get_text(" ", strip=True)) or "Kenya Law document"
        out.append(
            {
                "url": url,
                "title": title,
                "citation": "",
                "court": "",
                "date": "",
                "snippet": "",
            }
        )
    return out


def _parse_structured_list(items: list) -> list[dict]:
    out, seen = [], set()
    for item in items:
        if not isinstance(item, dict):
            continue
        url = (
            item.get("expression_frbr_uri")
            or item.get("frbr_uri")
            or item.get("url")
            or item.get("href")
            or ""
        )
        if not isinstance(url, str):
            continue
        canonical = canonical_eklr_url(url)
        if not canonical or canonical in seen:
            continue
        seen.add(canonical)
        out.append(
            {
                "url": canonical,
                "title": _clean(item.get("title") or item.get("name") or "")
                or "Kenya Law document",
                "citation": _clean(item.get("citation") or ""),
                "court": _clean(item.get("court") or ""),
                "date": _clean(item.get("date") or ""),
                "snippet": _clean(item.get("snippet") or ""),
            }
        )
    return out


def _walk_json_for_urls(payload) -> list[dict]:
    found, seen = [], set()

    def walk(obj, title_hint=""):
        if isinstance(obj, dict):
            url_field = (
                obj.get("expression_frbr_uri")
                or obj.get("frbr_uri")
                or obj.get("url")
                or obj.get("href")
                or ""
            )
            title_field = obj.get("title") or obj.get("name") or title_hint
            if isinstance(url_field, str):
                canonical = canonical_eklr_url(url_field)
                if canonical and canonical not in seen:
                    seen.add(canonical)
                    found.append(
                        {
                            "url": canonical,
                            "title": _clean(title_field) or "Kenya Law document",
                            "citation": _clean(obj.get("citation") or ""),
                            "court": _clean(obj.get("court") or ""),
                            "date": _clean(obj.get("date") or ""),
                            "snippet": _clean(obj.get("snippet") or ""),
                        }
                    )
            for v in obj.values():
                walk(v, title_field)
        elif isinstance(obj, list):
            for item in obj:
                walk(item, title_hint)
        elif isinstance(obj, str):
            for u in _scan_strings_for_urls(obj):
                if u not in seen:
                    seen.add(u)
                    found.append(
                        {
                            "url": u,
                            "title": "Kenya Law document",
                            "citation": "",
                            "court": "",
                            "date": "",
                            "snippet": "",
                        }
                    )

    walk(payload)
    return found


def parse_search_response(resp) -> list[dict]:
    if resp is None:
        return []
    text = resp.text or ""
    if not text.strip():
        return []
    ct = (resp.headers.get("Content-Type") or "").lower()
    payload = None
    if "json" in ct or text.lstrip().startswith(("{", "[")):
        try:
            payload = resp.json()
        except ValueError:
            payload = None
    if payload is not None:
        if isinstance(payload, dict):
            for key in ("results_html", "html", "fragment", "body", "content"):
                frag = payload.get(key)
                if isinstance(frag, str) and frag.strip():
                    docs = _parse_html_fragment(frag)
                    if docs:
                        return docs
        if isinstance(payload, dict):
            for key in ("results", "documents", "items", "data", "hits", "records"):
                items = payload.get(key)
                if isinstance(items, list) and items:
                    docs = _parse_structured_list(items)
                    if docs:
                        return docs
        docs = _walk_json_for_urls(payload)
        if docs:
            return docs
    return _parse_html_fragment(text)


_STOPWORDS = {
    "the",
    "and",
    "of",
    "in",
    "on",
    "at",
    "for",
    "to",
    "a",
    "an",
    "v",
    "vs",
    "versus",
    "re",
    "ex",
    "parte",
}


def query_variants(query: str) -> list[str]:
    q = _clean(query)
    if not q:
        return []
    words = [w for w in q.split() if len(w) > 1]
    variants = [q]
    if len(words) > 1:
        for i in range(len(words)):
            for j in range(i + 2, len(words) + 1):
                variants.append(" ".join(words[i:j]))
        for w in words:
            if len(w) > 4 and w.lower() not in _STOPWORDS:
                variants.append(w)
    seen, out = set(), []
    for v in variants:
        k = v.lower().strip()
        if k and k not in seen:
            seen.add(k)
            out.append(v)
    return out


def _eklr_search_once(q: str, kind: str, page: int = 1):
    uri_filter = "/akn/ke/act/" if kind == "statute" else "/akn/ke/judgment/"
    doc_type = "legislation" if kind == "statute" else "judgment"
    params = {"page": page, "search__all": f'("{q}")', "doc_type": doc_type}
    rate_limit()
    try:
        resp = KL._session.get(KL.BASE + KL.SEARCH_API, params=params, timeout=(4, 14))
    except requests.RequestException as exc:
        return [], f"network error: {exc.__class__.__name__}"
    if resp.status_code != 200:
        return [], f"HTTP {resp.status_code}"
    docs = parse_search_response(resp)
    return [d for d in docs if uri_filter in d["url"]], None


def search_live(query: str, kind: str, limit: int = 15):
    if not query:
        return [], None
    log.info("EKLR live search: %r kind=%s", query, kind)
    last_error = None
    docs = []
    for variant in query_variants(query):
        variant_docs, err = _eklr_search_once(variant, kind)
        if err:
            last_error = err
            continue
        if variant_docs:
            docs = variant_docs
            log.info("EKLR search %r → %d hits via %r", query, len(docs), variant)
            break
    if not docs and last_error is None:
        html_docs, html_err = KL.search_html(query, kind, limit=limit * 2)
        if html_err:
            last_error = html_err
        docs = html_docs
    if kind == "case":
        docs = [d for d in docs if is_case_url(d["url"])]
    elif kind == "statute":
        docs = [d for d in docs if is_act_url(d["url"])]
    if not docs:
        if last_error:
            log.info("EKLR search %r failed: %s", query, last_error)
        else:
            log.info("EKLR search %r: no hits", query)
        return [], last_error
    original_tokens = set(re.findall(r"[a-z0-9]+", query.lower()))
    if original_tokens:

        def score(d):
            text = (
                (d.get("title") or "")
                + " "
                + (d.get("citation") or "")
                + " "
                + (d.get("court") or "")
            ).lower()
            return sum(1 for t in original_tokens if t in text)

        docs.sort(key=score, reverse=True)
    for d in docs:
        try:
            save_document(
                {
                    "url": d["url"],
                    "kind": kind_for_url(d["url"], kind),
                    "title": d["title"],
                    "citation": d.get("citation", ""),
                    "court": d.get("court", ""),
                    "year": get_year(d.get("date", "")),
                    "date": d.get("date", ""),
                    "body": "",
                }
            )
        except Exception:
            pass
    return docs[:limit], last_error


_PDF_LINK_RE = re.compile(r'href="([^"]+\.pdf[^"]*)"', re.I)
_AKN_SELECTORS = (
    ".akn-akoma-ntoso",
    ".akn-act",
    ".akn-judgment",
    ".akn-doc",
    ".akn-body",
)
_NOISE_SELECTORS = (
    "nav",
    "header",
    "footer",
    "aside",
    "button",
    "script",
    "style",
    "noscript",
    "svg",
    "iframe",
    ".share",
    "[class*='share']",
    ".social",
    ".related",
    "[class*='related']",
    ".sidebar",
    ".breadcrumb",
    ".toolbar",
    ".actions",
    ".modal",
    ".toast",
    ".toc",
    "[class*='download']",
)
_AKN_PARA_CLASSES = ("akn-p", "akn-paragraph", "akn-heading", "akn-crossheading")


def _html_to_text(node) -> str:
    for br in node.find_all("br"):
        br.replace_with("\n")
    block_tags = [
        "p",
        "div",
        "h1",
        "h2",
        "h3",
        "h4",
        "h5",
        "h6",
        "li",
        "tr",
        "blockquote",
        "section",
        "article",
        "pre",
        "table",
        "dd",
        "dt",
        "dl",
        "figure",
        "figcaption",
    ]
    for tag in node.find_all(block_tags):
        try:
            tag.insert_before("\n\n")
            tag.append("\n\n")
        except Exception:
            pass
    for el in node.find_all(True):
        cls = " ".join(el.get("class") or [])
        if any(k in cls for k in _AKN_PARA_CLASSES):
            try:
                el.insert_before("\n\n")
            except Exception:
                pass
    raw = node.get_text()
    raw = re.sub(r"[ \t]+", " ", raw)
    raw = re.sub(r" ?\n ?", "\n", raw)
    return re.sub(r"\n{3,}", "\n\n", raw).strip()


def _extract_body_from_html(html: str) -> str:
    soup = BeautifulSoup(html, "html.parser")
    for sel in _NOISE_SELECTORS:
        try:
            for el in soup.select(sel):
                el.decompose()
        except Exception:
            pass
    best = ""
    for sel in _AKN_SELECTORS:
        for node in soup.select(sel):
            text = _html_to_text(node)
            if len(text) > len(best):
                best = text
        if len(best) > 3000:
            break
    if not best:
        for sel in ("article", "main"):
            node = soup.select_one(sel)
            if node:
                best = _html_to_text(node)
    return best


def _extract_pdf_text(pdf_bytes: bytes) -> str:
    if not _HAS_FITZ:
        return ""
    try:
        doc = fitz.open(stream=pdf_bytes, filetype="pdf")
        parts = [p.get_text() for p in doc]
        doc.close()
        text = "\n".join(parts)
        text = re.sub(r"[ \t]+", " ", text)
        return re.sub(r"\n{3,}", "\n\n", text).strip()
    except Exception as exc:
        log.debug("PDF extract failed: %s", exc)
        return ""


def _fetch_pdf_text(url: str) -> str:
    rate_limit()
    try:
        r = KL._session.get(url, timeout=(6, 40), allow_redirects=True)
    except requests.RequestException:
        return ""
    if not r.ok or not r.content.startswith(b"%PDF-"):
        return ""
    return _extract_pdf_text(r.content)


def fetch_document_content(url: str):
    r = KL.get(url + ".json", headers={"Accept": "application/json"}, timeout=(4, 20))
    if r is not None and "json" in (r.headers.get("Content-Type") or "").lower():
        try:
            payload = r.json()
            html = payload.get("content") or payload.get("body") or ""
            if isinstance(html, str) and html.strip():
                text = _extract_body_from_html(html)
                if len(text) > 500:
                    return text, ""
        except ValueError:
            pass
    r = KL.get(url, headers={"Accept": "text/html"}, timeout=(5, 25))
    if r is not None and "html" in (r.headers.get("Content-Type") or "").lower():
        text = _extract_body_from_html(r.text)
        m = _PDF_LINK_RE.search(r.text or "")
        pdf_url = urljoin(url, m.group(1)) if m else ""
        if len(text) > 500:
            return text, pdf_url
        if pdf_url:
            pdf_text = _fetch_pdf_text(pdf_url)
            if len(pdf_text) > 500:
                return pdf_text, pdf_url
    for candidate in (url + "/download", url + ".pdf"):
        pdf_text = _fetch_pdf_text(candidate)
        if len(pdf_text) > 500:
            return pdf_text, candidate
    return "", ""


def db():
    con = sqlite3.connect(str(DB_PATH), timeout=30)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA busy_timeout=30000")
    con.execute("PRAGMA synchronous=NORMAL")
    return con


def init_db():
    with db() as con:
        con.execute("PRAGMA journal_mode=WAL")
        con.execute("""
            CREATE TABLE IF NOT EXISTS documents (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                url TEXT NOT NULL UNIQUE,
                kind TEXT NOT NULL DEFAULT 'case',
                title TEXT NOT NULL DEFAULT '',
                citation TEXT NOT NULL DEFAULT '',
                court TEXT NOT NULL DEFAULT '',
                year TEXT NOT NULL DEFAULT '',
                date TEXT NOT NULL DEFAULT '',
                body TEXT NOT NULL DEFAULT '',
                pdf_path TEXT NOT NULL DEFAULT '',
                pdf_status TEXT NOT NULL DEFAULT 'not_found',
                aliases TEXT NOT NULL DEFAULT '[]',
                fetched_at REAL NOT NULL DEFAULT 0,
                accessed_at REAL NOT NULL DEFAULT 0
            )
        """)
        con.execute("CREATE INDEX IF NOT EXISTS idx_kind ON documents(kind)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_citation ON documents(citation)")


def get_year(text):
    m = re.search(r"\b(19|20)\d{2}\b", text or "")
    return m.group(0) if m else ""


def citation_from(text):
    for pat in (
        r"\[\d{4}\]\s*KESC\s*\d+",
        r"\[\d{4}\]\s*KECA\s*\d+",
        r"\[\d{4}\]\s*KEHC\s*\d+",
        r"\[\d{4}\]\s*KEELC\s*\d+",
        r"\[\d{4}\]\s*KEELRC\s*\d+",
        r"\[\d{4}\]\s*KE[A-Z]+\s*\d+",
    ):
        m = re.search(pat, text or "", re.I)
        if m:
            return _clean(m.group(0))
    return ""


def norm_title(s):
    return re.sub(r"[^a-z0-9]+", " ", (s or "").lower()).strip()


def save_document(item) -> int | None:
    url = canonical_eklr_url(item.get("url", ""))
    if not url:
        return None
    kind = kind_for_url(url, item.get("kind"))
    body = (item.get("body") or "")[:500_000]
    aliases = item.get("aliases") or []
    with db() as con:
        con.execute(
            """
            INSERT INTO documents(url,kind,title,citation,court,year,date,body,
                                  pdf_path,pdf_status,aliases,fetched_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?)
            ON CONFLICT(url) DO UPDATE SET
                kind=excluded.kind,
                title=CASE WHEN excluded.title!='' THEN excluded.title ELSE documents.title END,
                citation=CASE WHEN excluded.citation!='' THEN excluded.citation ELSE documents.citation END,
                court=CASE WHEN excluded.court!='' THEN excluded.court ELSE documents.court END,
                year=CASE WHEN excluded.year!='' THEN excluded.year ELSE documents.year END,
                date=CASE WHEN excluded.date!='' THEN excluded.date ELSE documents.date END,
                body=CASE WHEN excluded.body!='' THEN excluded.body ELSE documents.body END,
                pdf_path=CASE WHEN excluded.pdf_path!='' THEN excluded.pdf_path ELSE documents.pdf_path END,
                pdf_status=CASE WHEN excluded.body!='' THEN 'json' ELSE documents.pdf_status END,
                aliases=CASE WHEN excluded.aliases!='[]' THEN excluded.aliases ELSE documents.aliases END,
                fetched_at=CASE WHEN excluded.body!='' THEN excluded.fetched_at ELSE documents.fetched_at END
        """,
            (
                url,
                kind,
                _clean(item.get("title")),
                _clean(item.get("citation")),
                _clean(item.get("court")),
                _clean(item.get("year")),
                _clean(item.get("date")),
                body,
                item.get("pdf_path", ""),
                "json" if body else item.get("pdf_status", "not_found"),
                json.dumps(aliases),
                time.time() if body else 0,
            ),
        )
        row = con.execute("SELECT id FROM documents WHERE url=?", (url,)).fetchone()
    return row["id"] if row else None


def get_document(url):
    with db() as con:
        row = con.execute("SELECT * FROM documents WHERE url=?", (url,)).fetchone()
    return dict(row) if row else None


def ensure_document(url: str, kind_hint=None):
    url = canonical_eklr_url(url)
    if not url:
        return None
    doc = get_document(url)
    if doc and doc.get("body"):
        return doc
    text, pdf_url = fetch_document_content(url)
    if not text:
        if not doc:
            save_document(
                {
                    "url": url,
                    "kind": kind_for_url(url, kind_hint),
                    "title": "",
                    "body": "",
                }
            )
        doc = get_document(url) or {}
        if doc:
            doc["pdf_only"] = True
        return doc or None
    if not doc:
        doc = {"url": url, "kind": kind_for_url(url, kind_hint)}
    save_document(
        {
            "url": url,
            "kind": kind_for_url(url, kind_hint or doc.get("kind")),
            "title": doc.get("title") or "",
            "citation": doc.get("citation") or citation_from(text[:5000]),
            "court": doc.get("court") or "",
            "year": doc.get("year") or get_year(text[:2000]),
            "body": text,
            "pdf_path": pdf_url,
        }
    )
    fresh = get_document(url) or {}
    if pdf_url and not fresh.get("pdf_path"):
        fresh["pdf_url"] = pdf_url
    if not fresh.get("body"):
        fresh["pdf_only"] = True
    return fresh


def _enqueue_fetch(url: str, kind: str):
    with _inflight_lock:
        if url in _inflight:
            return
        _inflight.add(url)

    def _run():
        try:
            ensure_document(url, kind)
        except Exception as exc:
            log.debug("enrich failed %s: %s", url, exc)
        finally:
            with _inflight_lock:
                _inflight.discard(url)

    FETCH_POOL.submit(_run)


ACTS_MANIFEST_JSON = r"""[
  {"title": "Access to Information Act", "cap": "Cap. 7M"},
  {"title": "Accountants Act", "cap": "Cap. 531"},
  {"title": "Advocates Act", "cap": "Cap. 16"},
  {"title": "Arbitration Act", "cap": "Cap. 49"},
  {"title": "Banking Act", "cap": "Cap. 488"},
  {"title": "Basic Education Act", "cap": "No. 14 of 2013"},
  {"title": "Bills of Exchange Act", "cap": "Cap. 27"},
  {"title": "Capital Markets Act", "cap": "Cap. 485A"},
  {"title": "Central Bank of Kenya Act", "cap": "Cap. 491"},
  {"title": "Children Act", "cap": "No. 8 of 2001"},
  {"title": "Civil Procedure Act", "cap": "Cap. 21"},
  {"title": "Climate Change Act", "cap": "No. 11 of 2016"},
  {"title": "Companies Act", "cap": "No. 17 of 2015"},
  {"title": "Competition Act", "cap": "No. 12 of 2010"},
  {"title": "Computer Misuse and Cybercrimes Act", "cap": "No. 5 of 2018"},
  {"title": "Consumer Protection Act", "cap": "No. 46 of 2012"},
  {"title": "County Governments Act", "cap": "No. 17 of 2012"},
  {"title": "Criminal Procedure Code", "cap": "Cap. 75"},
  {"title": "Data Protection Act", "cap": "No. 24 of 2019"},
  {"title": "Elections Act", "cap": "No. 24 of 2011"},
  {"title": "Employment Act", "cap": "Cap. 226"},
  {"title": "Energy Act", "cap": "No. 1 of 2019"},
  {"title": "Ethics and Anti-Corruption Act", "cap": "No. 22 of 2011"},
  {"title": "Evidence Act", "cap": "Cap. 80"},
  {"title": "Government Contracts Act", "cap": "Cap. 25"},
  {"title": "Health Act", "cap": "Cap. 241"},
  {"title": "HIV and AIDS Prevention and Control Act", "cap": "Cap. 246A"},
  {"title": "Income Tax Act", "cap": "Cap. 470"},
  {"title": "Insurance Act", "cap": "Cap. 487"},
  {"title": "Judicature Act", "cap": "Cap. 8"},
  {"title": "Judiciary Act", "cap": "Cap. 8"},
  {"title": "Kadhis' Courts Act", "cap": "Cap. 11"},
  {"title": "Kenya Citizenship and Immigration Act", "cap": "No. 12 of 2011"},
  {"title": "Labour Relations Act", "cap": "No. 14 of 2007"},
  {"title": "Land Act", "cap": "No. 6 of 2012"},
  {"title": "Land Registration Act", "cap": "No. 3 of 2012"},
  {"title": "Law of Contract Act", "cap": "Cap. 23"},
  {"title": "Law of Succession Act", "cap": "Cap. 160"},
  {"title": "Leadership and Integrity Act", "cap": "No. 19 of 2012"},
  {"title": "Legal Aid Act", "cap": "No. 6 of 2016"},
  {"title": "Magistrates' Courts Act", "cap": "Cap. 10"},
  {"title": "Marriage Act", "cap": "No. 4 of 2014"},
  {"title": "Mining Act", "cap": "No. 12 of 2016"},
  {"title": "National Police Service Act", "cap": "No. 11A of 2011"},
  {"title": "Penal Code", "cap": "Cap. 63"},
  {"title": "Petroleum Act", "cap": "No. 2 of 2019"},
  {"title": "Political Parties Act", "cap": "No. 11 of 2011"},
  {"title": "Public Finance Management Act", "cap": "No. 18 of 2012"},
  {"title": "Public Health Act", "cap": "Cap. 242"},
  {"title": "Public Procurement and Asset Disposal Act", "cap": "No. 33 of 2015"},
  {"title": "Retirement Benefits Act", "cap": "No. 3 of 1997"},
  {"title": "Sexual Offences Act", "cap": "No. 3 of 2006"},
  {"title": "Standards Act", "cap": "Cap. 496"},
  {"title": "Stamp Duty Act", "cap": "Cap. 480"},
  {"title": "State Corporations Act", "cap": "Cap. 446"},
  {"title": "Statutory Instruments Act", "cap": "No. 23 of 2013"},
  {"title": "Tax Procedures Act", "cap": "No. 29 of 2015"},
  {"title": "Traffic Act", "cap": "Cap. 403"},
  {"title": "Universities Act", "cap": "No. 42 of 2012"},
  {"title": "Urban Areas and Cities Act", "cap": "No. 13 of 2011"},
  {"title": "Value Added Tax Act", "cap": "No. 35 of 2013"},
  {"title": "Water Act", "cap": "No. 43 of 2016"},
  {"title": "Work Injury Benefits Act", "cap": "No. 13 of 2007"}
]"""


def load_acts_manifest() -> list[dict]:
    if not ACTS_JSON_PATH.exists():
        try:
            ACTS_JSON_PATH.write_text(ACTS_MANIFEST_JSON, encoding="utf-8")
        except Exception as exc:
            log.warning("acts.json write failed: %s", exc)
    try:
        data = json.loads(ACTS_JSON_PATH.read_text(encoding="utf-8"))
        seen, out = set(), []
        for a in data:
            t = (a.get("title") or "").strip()
            if t and t.lower() not in seen:
                seen.add(t.lower())
                out.append(a)
        return out
    except Exception as exc:
        log.warning("acts.json read failed: %s", exc)
        return []


_const_cache = None
_const_lock = threading.Lock()
_ROMAN = {"i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x"}


def load_constitution() -> list:
    global _const_cache
    if _const_cache is not None:
        return _const_cache
    with _const_lock:
        if _const_cache is None:
            try:
                _const_cache = json.loads(
                    CONSTITUTION_JSON_PATH.read_text(encoding="utf-8")
                )
            except Exception:
                _const_cache = []
    return _const_cache


def constitution_toc() -> list:
    chapters: dict[int, dict] = {}
    for art in load_constitution():
        ch = art.get("chapter")
        if not ch or len(ch) < 2:
            continue
        node = chapters.setdefault(
            ch[0],
            {
                "number": ch[0],
                "title": ch[1],
                "parts": {},
                "articles": [],
            },
        )
        part = art.get("part")
        if part and len(part) >= 2:
            p = node["parts"].setdefault(
                part[0],
                {
                    "number": part[0],
                    "title": part[1],
                    "articles": [],
                },
            )
            p["articles"].append({"number": art["number"], "title": art["title"]})
        else:
            node["articles"].append({"number": art["number"], "title": art["title"]})
    return [
        {
            **chapters[n],
            "parts": [chapters[n]["parts"][k] for k in sorted(chapters[n]["parts"])],
        }
        for n in sorted(chapters)
    ]


_MARKER_START = re.compile(r"^\((\d{1,3}|[a-zA-Z]{1,3})\)\s*")


def constitution_paragraphs(lines: list[str]) -> list[dict]:
    merged: list[str] = []
    for raw in lines or []:
        line = (raw or "").strip()
        if not line:
            continue
        if _MARKER_START.match(line) or not merged:
            merged.append(line)
        else:
            merged[-1] += " " + line
    entries = []
    for line in merged:
        m = re.match(r"^(\((?:\d{1,3}|[a-zA-Z]{1,3})\))\s*(.*)$", line, re.S)
        entries.append(
            {"marker": m.group(1), "text": m.group(2).strip()}
            if m
            else {"marker": "", "text": line}
        )
    for i, e in enumerate(entries):
        inner = e["marker"].strip("().").lower()
        if not inner or inner.isdigit():
            e["level"] = 0
        elif inner == "i":
            nxt = next(
                (
                    entries[j]["marker"].strip("().").lower()
                    for j in range(i + 1, min(i + 5, len(entries)))
                    if entries[j]["marker"]
                ),
                "",
            )
            e["level"] = 2 if nxt in _ROMAN else 1
        else:
            e["level"] = 1
    return entries


_AKN_META_LABELS = frozenset(
    [
        "Judges",
        "Judge",
        "Judgment date",
        "Language",
        "Case action",
        "Outcome",
        "Docket Number",
        "Citation",
        "Court",
        "Date",
        "Skip to document content",
        "Document detail",
        "Flynote",
        "Area of law",
        "Summary",
        "Held",
        "Reported",
        "Cases cited",
        "Legislation cited",
    ]
)


def _strip_metadata_prefix(body: str) -> str:
    if not body:
        return body
    if "Skip to document content" in body:
        idx = body.rindex("Skip to document content")
        body = body[idx + len("Skip to document content") :].lstrip("\n\t ")
    lines = body.split("\n")
    for i, line in enumerate(lines[:60]):
        if line.strip() in _AKN_META_LABELS:
            for j in range(i + 1, min(i + 100, len(lines))):
                nxt = lines[j].strip()
                if re.match(r"^REPUBLIC\s+OF\s+KENYA\s*$", nxt, re.I):
                    body = "\n".join(lines[j:])
                    break
                if re.match(r"^IN\s+THE\s+", nxt, re.I):
                    body = "\n".join(lines[j:])
                    break
            break
    low = body.lower()
    marker_idx = -1
    for m in ("to the top", "related documents"):
        idx = low.rfind(m)
        if idx > marker_idx:
            marker_idx = idx
    if marker_idx >= 0:
        end_of_marker = marker_idx
        while end_of_marker < len(body) and body[end_of_marker] not in " \n\t▲":
            end_of_marker += 1
        before = body[:marker_idx].rstrip()
        after = body[end_of_marker:].lstrip("\n\t ▲")
        before_paras = before.count("\n\n")
        after_paras = after.count("\n\n")
        if len(after) > 500 and after_paras > max(before_paras, 2):
            has_header_before = re.search(
                r"^\s*REPUBLIC\s+OF\s+KENYA", before, re.I | re.M
            )
            has_header_after = re.search(
                r"^\s*REPUBLIC\s+OF\s+KENYA", after, re.I | re.M
            )
            if has_header_before and not has_header_after:
                m = re.search(
                    r"\b(?:R\s*U\s*L\s*I\s*N\s*G|J\s*U\s*D\s*G\s*M\s*E\s*N\s*T|"
                    r"RULING|JUDGMENT|DECISION|ORDER|AWARD|SENTENCE)\b",
                    before,
                    re.I,
                )
                if m:
                    body = before[: m.end()] + "\n\n" + after
                else:
                    body = before + "\n\n" + after
            else:
                body = after
        else:
            body = before
    body = re.sub(r"^[\s▲]+", "", body)
    return body.lstrip()


def _reparagraph_glued(text: str) -> str:
    for pat in (r"R\s+U\s+L\s+I\s+N\s+G", r"J\s+U\s+D\s+G\s+M\s+E\s+N\s+T"):
        text = re.sub(
            r"(?<=[A-Za-z\s\.\-&,])" + pat + r"(?=[\s\.])",
            lambda m: "\n\n" + m.group(0) + "\n\n",
            text,
        )
    text = re.sub(
        r"([A-Z][A-Z\s\.\-&,]{15,})\s+(RULING|JUDGMENT|DECISION)\s+(?=[A-Z][a-z])",
        r"\1\n\n\2\n\n",
        text,
    )
    return text


_PARA_START_CUE = re.compile(
    r"(?<=[.!?])\s+"
    r"(?=(?:On\s+\d{1,2}[/\.\-]\d{1,2}[/\.\-]\d{2,4}\b"
    r"|The\s+court\s+(?:then|thence|could|is|was|has|had|noted|found)"
    r"|I\s+have\s+(?:considered|noted|read|seen)"
    r"|It\s+(?:is|was|would)\s+"
    r"|Having\s+"
    r"|In\s+(?:the|my|this)\s+"
    r"|(?:Dated|DATED)\s+and\s+(?:delivered|signed)\b))",
    re.I,
)


def _split_blob(text: str) -> str:
    if not text or len(text) < 500:
        return text
    parts = _PARA_START_CUE.split(text)
    if len(parts) < 3:
        return text
    return "\n\n".join(p.strip() for p in parts if p.strip())


def _prenumber_blocks(blocks: list[str]) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(blocks):
        b = blocks[i].strip()
        m = re.match(r"^\[?(\d{1,4})\]?\.?\s*$", b)
        if m and i + 1 < len(blocks):
            num = int(m.group(1))
            nxt = blocks[i + 1].strip()
            if (
                1 <= num <= 999
                and nxt
                and not re.match(r"^\[?(\d{1,4})\]?\.?\s*$", nxt)
                and not re.match(r"^[*\-\s_=•]+$", nxt)
            ):
                out.append(f"{num}. {nxt}")
                i += 2
                continue
        m = re.match(r"^(\d{1,4})\s*\n\s*(\S.*)$", b, re.S)
        if m:
            num = int(m.group(1))
            if 1 <= num <= 999:
                out.append(f"{num}. {m.group(2).strip()}")
                i += 1
                continue
        out.append(b)
        i += 1
    return out


_REPUBLIC_RE = re.compile(r"^\s*REPUBLIC\s+OF\s+KENYA\s*$", re.I)
_CORAM_RE = re.compile(r"^\s*\(?\s*CORAM\s*:?\s*(.+?)\)?\s*$", re.I)
_CASE_NUM_RE = re.compile(
    r"^\s*("
    r"(?:CIVIL|CRIMINAL|MISC(?:ELLANEOUS)?|CONSTITUTIONAL|ELECTION|"
    r"PETITION|APPEAL|SUIT|CAUSE|COMMERCIAL|JUDICIAL\s+REVIEW|"
    r"HCC|HCCC|HCCRC|HCCR|CMCC|CMCR|ELC|ELRC|KEHC|KECA|KESC|JR|TRIBUNAL)"
    r"[A-Z\.\s]*?"
    r"(?:NO\.?|NUMBER)?\s*"
    r"[A-Z]?\d+[A-Z\d]*"
    r"[\s\d,&/]*?\s+OF\s+\d{4}"
    r"(?:\s*\([^)]*\))?"
    r")\s*$",
    re.I,
)
_JUDGE_RE = re.compile(
    r"^\s*([A-Z][A-Za-z\.\s\-&',]{1,50}?)\s*,\s*(J|JA|JJA|JSC|CJ|DCJ|P|"
    r"J\.|JA\.|JJA\.|JSC\.|P\.)\s*\.?\s*$",
    re.I,
)
_DATE_RE = re.compile(
    r"^\s*((?:JANUARY|FEBRUARY|MARCH|APRIL|MAY|JUNE|JULY|AUGUST|SEPTEMBER|"
    r"OCTOBER|NOVEMBER|DECEMBER)\s+\d{1,2},?\s+\d{4}"
    r"|\d{1,2}(?:ST|ND|RD|TH)?\s+(?:DAY\s+OF\s+)?"
    r"(?:JANUARY|FEBRUARY|MARCH|APRIL|MAY|JUNE|JULY|AUGUST|SEPTEMBER|"
    r"OCTOBER|NOVEMBER|DECEMBER)\s*,?\s*\d{4})\s*$",
    re.I,
)
_DIVIDER_RE = re.compile(r"^\s*(BETWEEN|AND|VERSUS|VS\.?)\s*$", re.I)
_DOC_TYPE_RE = re.compile(
    r"^\s*((?:R\s*U\s*L\s*I\s*N\s*G|J\s*U\s*D\s*G\s*M\s*E\s*N\s*T|"
    r"RULING|JUDGMENT|DECISION|ORDER|AWARD|SENTENCE|"
    r"JUDGMENT\s+OF\s+THE\s+COURT|RULING\s+OF\s+THE\s+COURT|"
    r"JUDGMENT\s+AND\s+DECREE|RULING\s+AND\s+ORDER))\s*$",
    re.I,
)
_ROLE_AT_END_RE = re.compile(
    r"^(.*?)[\s\.\u2026]+((?:\d{1,2}(?:ST|ND|RD|TH)\s+)?"
    r"(?:APPELLANT|RESPONDENT|PLAINTIFF|DEFENDANT|PETITIONER|"
    r"INTERESTED\s+PARTY|INTENDED\s+APPELLANT|INTENDED\s+RESPONDENT|"
    r"APPLICANT|OBJECTOR|ACCUSED|CONVICT|PROSECUTOR))\s*\.?\s*$",
    re.I,
)
_PURE_ROLE_RE = re.compile(
    r"^\s*(?:\d{1,2}(?:ST|ND|RD|TH)\s+)?"
    r"(?:APPELLANT|RESPONDENT|PLAINTIFF|DEFENDANT|PETITIONER|"
    r"INTERESTED\s+PARTY|APPLICANT|OBJECTOR|ACCUSED|CONVICT|PROSECUTOR)"
    r"\s*\.?\s*$",
    re.I,
)
_NUMBERED_PARA_RE = re.compile(r"^\s*\[?(\d{1,4})\]?\s*[\.\)]\s+")
_SUBITEM_RE = re.compile(
    r"^\s*(\((?:\d{1,2}|[a-z]{1,3})\)|[a-z]{1,3}[\.\)])\s+",
    re.I,
)
_TRAILING_DOTS_RE = re.compile(r"[\s\.\u2026]+$")
_MATTER_OF_RE = re.compile(r"^IN\s+THE\s+MATTER\s+OF\b", re.I)
_QUOTE_INTRO_RE = re.compile(r'[-:]\s*["\u201c\u201d\u2018\u2019]\s*$')


def _is_quote_block(block: str, prev_block: str = "") -> bool:
    b = block.strip()
    if not b:
        return False
    if re.match(r'^["\u201c\u2018]', b):
        return True
    if prev_block and _QUOTE_INTRO_RE.search(prev_block.strip()):
        return True
    return False


def _combine_party_objs(items: list[dict]) -> list[dict]:
    out, cur_raw, cur_side = [], "", None
    for it in items:
        raw, side = it["raw"], it["side"]
        if cur_raw and cur_side == side:
            cur_raw += " " + raw
        else:
            if cur_raw:
                out.append(_finalize_party(cur_raw, cur_side))
            cur_raw, cur_side = raw, side
        if _ROLE_AT_END_RE.match(cur_raw):
            out.append(_finalize_party(cur_raw, cur_side))
            cur_raw, cur_side = "", None
    if cur_raw:
        out.append(_finalize_party(cur_raw, cur_side))
    return out


def _finalize_party(raw: str, side) -> dict:
    raw = _clean(raw)
    m = _ROLE_AT_END_RE.match(raw)
    if m:
        name = _TRAILING_DOTS_RE.sub("", _clean(m.group(1)))
        role = _clean(m.group(2)).upper()
        if name and (len(name) >= 4 or " " in name):
            return {"name": name, "role": role, "side": side or "before"}
    name = _TRAILING_DOTS_RE.sub("", raw)
    return {"name": name, "role": "", "side": side or "before"}


def case_header(body: str) -> dict:
    lines = [l.strip() for l in (body or "").split("\n") if l.strip()]
    start = None
    for i, l in enumerate(lines):
        if _REPUBLIC_RE.match(l) or re.match(r"^IN\s+THE\s+", l, re.I):
            start = i
            break
    if start is None:
        return {"body_start": 0, "parties": []}
    end = len(lines)
    doc_type = ""
    for i in range(start, min(start + 200, len(lines))):
        l = lines[i]
        m = _DOC_TYPE_RE.match(l)
        if m:
            doc_type = _clean(m.group(1)).upper()
            end = i + 1
            break
        if _NUMBERED_PARA_RE.match(l):
            end = i
            break
    republic = ""
    court = ""
    division_parts: list[str] = []
    matter_parts: list[str] = []
    case_number = ""
    coram = ""
    judges: list[str] = []
    dates: list[str] = []
    divider = ""
    raw_parties: list[dict] = []
    paren_parts: list[str] = []
    state = "before"
    seen_case_num = False
    in_paren = False
    for l in lines[start:end]:
        if in_paren:
            paren_parts.append(l)
            if l.rstrip().endswith(")"):
                in_paren = False
            continue
        if _REPUBLIC_RE.match(l):
            republic = "REPUBLIC OF KENYA"
            continue
        if _CORAM_RE.match(l):
            coram = l if l.startswith("(") else f"({l})"
            continue
        m = _CASE_NUM_RE.match(l)
        if m:
            case_number = _clean(m.group(1))
            seen_case_num = True
            continue
        if not court and re.match(r"^IN\s+THE\s+", l, re.I):
            court = l
            continue
        m = _JUDGE_RE.match(l)
        if m:
            judges.append(l)
            continue
        m = _DATE_RE.match(l)
        if m:
            dates.append(_clean(m.group(1)).upper())
            continue
        m = _DIVIDER_RE.match(l)
        if m:
            d = m.group(1).upper()
            divider = divider or d
            if d in ("VERSUS", "VS", "VS.", "AND") and raw_parties:
                state = "after"
            continue
        if _DOC_TYPE_RE.match(l):
            continue
        if _MATTER_OF_RE.match(l):
            matter_parts.append(l)
            continue
        if _PURE_ROLE_RE.match(l):
            if raw_parties:
                raw_parties[-1]["raw"] += " " + l
                continue
            raw_parties.append({"raw": l, "side": state})
            continue
        if not seen_case_num and l.startswith("("):
            division_parts.append(l)
            continue
        if not seen_case_num and re.match(r"^[A-Z][A-Z\s&,\.\-()']{2,90}$", l):
            division_parts.append(l)
            continue
        if l.startswith("(") and seen_case_num:
            paren_parts.append(l)
            in_paren = not l.rstrip().endswith(")")
            continue
        raw_parties.append({"raw": l, "side": state})
    parties = _combine_party_objs(raw_parties)
    return {
        "republic": republic,
        "court": court,
        "division": " ".join(division_parts),
        "matter": " ".join(matter_parts),
        "case_number": case_number,
        "coram": coram,
        "judges": judges,
        "date": dates[0] if dates else "",
        "dates": dates,
        "divider": divider,
        "parties": parties,
        "parenthetical": " ".join(paren_parts),
        "doc_type": doc_type,
        "body_start": end,
    }


def _normalize_for_party(s: str) -> str:
    return re.sub(r"[\.\s\u2026_]+", " ", (s or "").upper()).strip()


_ROLE_KW_RE = re.compile(
    r"\b(APPELLANT|RESPONDENT|PLAINTIFF|DEFENDANT|PETITIONER|APPLICANT|"
    r"ACCUSED|CONVICT|INTERESTED\s+PARTY|OBJECTOR|PROSECUTOR)\b",
    re.I,
)


def _skip_secondary_title_block(rest: str, header: dict) -> str:
    if not rest:
        return rest
    lines = rest.split("\n")
    scan_end = min(40, len(lines))
    party_names: set[str] = set()
    for p in header.get("parties") or []:
        n = _normalize_for_party(p.get("name") or "")
        if len(n) > 3:
            party_names.add(n)
    saw_divider = False
    saw_party = False
    in_paren = False
    for i in range(scan_end):
        stripped = lines[i].strip()
        if not stripped:
            continue
        m = _DOC_TYPE_RE.match(stripped)
        if m:
            if saw_divider or saw_party:
                return "\n".join(lines[i + 1 :]).lstrip("\n\t ")
            break
        if in_paren:
            if ")" in stripped:
                in_paren = False
            continue
        if stripped.startswith("("):
            if ")" not in stripped:
                in_paren = True
            continue
        if _DIVIDER_RE.match(stripped):
            saw_divider = True
            continue
        if len(stripped) < 80:
            upper = _normalize_for_party(stripped)
            is_party = any(pn in upper for pn in party_names)
            if not is_party and _ROLE_KW_RE.search(upper):
                is_party = True
            if is_party:
                saw_party = True
                continue
        if len(stripped) <= 100:
            continue
        break
    return rest


def _intro_ending(text: str) -> bool:
    t = (text or "").rstrip()
    return t.endswith(":") or bool(
        re.search(
            r"\b(as follows|namely|the following|hereunder|thus)\s*[:.]?\s*$",
            t,
            re.I,
        )
    )


def _looks_like_case_heading(text: str) -> bool:
    if len(text) > 100 or len(text.split()) > 12:
        return False
    stripped = text.rstrip()
    if stripped.endswith((".", "!", "?", ";", ",", ":")):
        return False
    if text.isupper():
        return True
    words = text.split()
    if not words:
        return False
    if len(words) == 1:
        return words[0][:1].isupper()
    caps = sum(1 for w in words if w[:1].isupper())
    return caps >= max(2, int(len(words) * 0.7))


def _case_sub_level(marker: str) -> int:
    inner = marker.strip("().").lower()
    if inner.isdigit():
        return 1
    if inner in _ROMAN:
        return 3
    return 2


def case_body_items(body: str) -> list[dict]:
    body = _reparagraph_glued(body or "")
    body = re.sub(r"[ \t]+", " ", body)
    body = re.sub(r"\n{3,}", "\n\n", body)
    body = _split_blob(body)
    blocks = [b.strip() for b in re.split(r"\n{2,}", body) if b.strip()]
    blocks = _prenumber_blocks(blocks)
    out: list[dict] = []
    last_para: dict | None = None
    last_number = 0
    prev_block = ""
    for block in blocks:
        if re.match(r"^[*\-\s_=•]+$", block):
            continue
        m = re.match(r"^\s*\[?(\d{1,4})\]?\s*[\.\)]\s*(.*)$", block, re.S)
        if m:
            n = int(m.group(1))
            text = m.group(2).strip()
            if (
                last_para is not None
                and n <= 3
                and last_number >= 4
                and _intro_ending(last_para.get("text", ""))
            ):
                last_para.setdefault("items", []).append(
                    {"marker": f"{n}.", "level": 1, "text": text}
                )
                prev_block = block
                continue
            para = {"type": "para", "number": n, "text": text}
            out.append(para)
            last_para = para
            last_number = n
            prev_block = block
            continue
        m = _SUBITEM_RE.match(block)
        if m:
            marker = m.group(1)
            text = block[m.end() :].strip()
            level = _case_sub_level(marker)
            if last_para is not None:
                last_para.setdefault("items", []).append(
                    {"marker": marker, "level": level, "text": text}
                )
            else:
                out.append(
                    {"type": "subitem", "marker": marker, "level": level, "text": text}
                )
            prev_block = block
            continue
        if _is_quote_block(block, prev_block):
            if last_para is not None:
                last_para.setdefault("continuations", []).append(
                    {"type": "quote", "text": block}
                )
            else:
                out.append({"type": "quote", "text": block})
            prev_block = block
            continue
        if _looks_like_case_heading(block):
            out.append({"type": "heading", "text": block})
            last_para = None
            prev_block = block
            continue
        if last_para is not None:
            last_para.setdefault("continuations", []).append(
                {"type": "text", "text": block}
            )
        else:
            out.append({"type": "plain", "text": block})
        prev_block = block
    return out


_SIGN_DATE_RE = re.compile(r"^((?:DATED|Dated)[^\n]*?\b\d{4})\s*\.?", re.I)
_SIGN_ROLE_RE = re.compile(
    r"\b(JUDGE\s+OF\s+APPEAL|JUDGE|JUSTICE\s+OF\s+APPEAL|"
    r"PRESIDENT(?:\s+OF\s+THE\s+COURT\s+OF\s+APPEAL)?|"
    r"DEPUTY\s+REGISTRAR|REGISTRAR)\b",
    re.I,
)
_PRESENCE_RE = re.compile(r"IN\s+THE\s+PRESENCE\s+OF\s*:?", re.I)
_APPEARANCE_ROLE_RE = re.compile(
    r"(For\s+the\s+[A-Za-z]+(?:\s*/\s*[A-Za-z]+)?|"
    r"For\s+[A-Za-z]+|Absent|Present|"
    r"C\s*/\s*A|Court\s+Assistant|"
    r"Holding\s+Brief|h/b\s+for\s+[A-Za-z\s]+)",
    re.I,
)
_SIGN_NOISE_RE = re.compile(
    r"\s*(?:Related documents|RELATED DOCUMENTS|To the top|TO THE TOP|▲)\s*$",
    re.I,
)


def _parse_signatories(text: str) -> list[dict]:
    text = re.sub(r"[.\u2026_]{3,}", " ", text or "")
    text = _clean(text)
    if not text:
        return []
    out: list[dict] = []
    pos = 0
    for m in _SIGN_ROLE_RE.finditer(text):
        name = _clean(text[pos : m.start()].strip(" ,;."))
        role = m.group(1).upper()
        if name:
            out.append({"name": name, "title": role})
        elif out:
            out[-1]["title"] = role
        pos = m.end()
    rest = _clean(text[pos:].strip(" ,;."))
    if rest:
        if out:
            out[-1]["title"] = f"{out[-1]['title']} {rest.upper()}".strip()
        else:
            out.append({"name": rest, "title": "JUDGE"})
    return out


def _parse_appearances(text: str) -> list[dict]:
    text = re.sub(r"[.\u2026_]{3,}", " ", text or "").strip()
    if not text:
        return []
    out: list[dict] = []
    pos = 0
    for m in _APPEARANCE_ROLE_RE.finditer(text):
        name = _clean(text[pos : m.start()].strip(" ,;."))
        role = _clean(m.group(1))
        if name:
            out.append({"name": name, "role": role})
        elif out:
            out[-1]["role"] = role
        pos = m.end()
    rest = _clean(text[pos:].strip(" ,;."))
    if rest:
        if out:
            out[-1]["role"] = f"{out[-1]['role']} {rest}".strip()
        else:
            out.append({"name": rest, "role": ""})
    return out


def case_signing(text: str) -> dict:
    text = _SIGN_NOISE_RE.sub("", text or "").strip()
    if not text:
        return {"date_line": "", "signatories": [], "appearances": []}
    date_line = ""
    m = _SIGN_DATE_RE.match(text)
    if m:
        date_line = _clean(m.group(1))
        if not date_line.endswith("."):
            date_line += "."
        text = text[m.end() :].strip()
    appearances: list[dict] = []
    pm = _PRESENCE_RE.search(text)
    if pm:
        appearances = _parse_appearances(text[pm.end() :])
        text = text[: pm.start()].strip()
    signatories = _parse_signatories(text)
    return {
        "date_line": date_line,
        "signatories": signatories,
        "appearances": appearances,
    }


def build_case_view(doc: dict) -> dict:
    body = re.sub(r"[ \t]+", " ", doc.get("body") or "")
    body = re.sub(r"\n{3,}", "\n\n", body)
    body = _strip_metadata_prefix(body)
    body = _reparagraph_glued(body)
    body = _split_blob(body)
    header = case_header(body)
    start = header.get("body_start", 0)
    rest = "\n".join(body.split("\n")[start:]).strip()
    rest = _skip_secondary_title_block(rest, header)
    blocks = re.split(r"\n{2,}", rest)
    signing_raw = ""
    for i, b in enumerate(blocks):
        if re.match(r"^\s*(?:DATED|Dated)\b", b):
            signing_raw = "\n\n".join(x.strip() for x in blocks[i:] if x.strip())
            blocks = blocks[:i]
            break
    signing = (
        case_signing(signing_raw)
        if signing_raw
        else {"date_line": "", "signatories": [], "appearances": []}
    )
    paragraphs = case_body_items("\n\n".join(blocks))
    return {
        "kind": "case",
        "url": doc.get("url", ""),
        "title": doc.get("title") or "Untitled judgment",
        "citation": doc.get("citation") or "",
        "year": doc.get("year") or "",
        "republic": header.get("republic", ""),
        "court": header.get("court", ""),
        "division": header.get("division", ""),
        "matter": header.get("matter", ""),
        "case_number": header.get("case_number", ""),
        "coram": header.get("coram", ""),
        "judges": header.get("judges", []),
        "date": header.get("date", ""),
        "dates": header.get("dates", []),
        "divider": header.get("divider", ""),
        "parties": header.get("parties", []),
        "parties_before": [
            f"{p['name']} — {p['role']}"
            for p in header.get("parties", [])
            if p.get("side") == "before" and p.get("role")
        ],
        "parties_after": [
            f"{p['name']} — {p['role']}"
            for p in header.get("parties", [])
            if p.get("side") == "after" and p.get("role")
        ],
        "parenthetical": header.get("parenthetical", ""),
        "doc_type": header.get("doc_type", ""),
        "paragraphs": paragraphs,
        "body": paragraphs,
        "signing": signing,
        "signing_block": signing,
        "signing_raw": signing_raw,
        "pdf_only": bool(doc.get("pdf_only")),
        "pdf_url": doc.get("pdf_path") or "",
    }


_PART_RE = re.compile(
    r"^(?:Part|PART)\s+([IVXLCDM]+[A-Z]?)\s*[—\-–:.\s]+\s*(.*)$",
    re.I,
)
_SECTION_RE = re.compile(r"^(\d{1,3}[A-Z]?)\.\s+(.*)$", re.S)
_META_LINE_RE = re.compile(
    r"^(Published\s+in(?:\s+the)?\s+Kenya\s+Gazette|"
    r"Assented\s+to|Commenced|In\s+force|Revised\s+by)"
    r"\s*(?:on)?\s*(.+)$",
    re.I,
)
_ACT_HEADING_RE = re.compile(
    r"^(.+?)\s+(?:NO\.?\s*\d+\s+OF\s+\d{4}|CAP\.?\s*\d+[A-Z]?)$",
    re.I,
)
_PURE_MARKER_RE = re.compile(r"^\s*\((?:\d{1,3}|[a-z]{1,3})\)\s*\.?\s*$", re.I)
_STARTS_MARKER_RE = re.compile(r"^\s*\((?:\d{1,3}|[a-z]{1,3})\)", re.I)
_CONJUNCTION_RE = re.compile(r"^\s*(?:and|or|&|but|nor)\s*$", re.I)
_NUM_START = re.compile(r"^\d{1,3}[A-Z]?\.\s", re.I)

# BROADENED: matches markers preceded by ANY punctuation, followed by ANY
# whitespace (including inline text).  This catches both:
#   "...limited to— (a)\n\ninformation..."    (trailing marker)
#   "...individual; (e) a person's opinion..."  (inline marker)
_MARKER_PUNCT_RE = re.compile(
    r"([.;:,—–\-])\s*(\(\d{1,3}\)|\([a-z]\)|\([ivxlc]{2,}\))\s*",
    re.MULTILINE,
)


def _normalize_markers(text: str) -> str:
    if not text:
        return text
    # Normalise Windows CRLF first so downstream splits work
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    return _MARKER_PUNCT_RE.sub(r"\1\n\n\2 ", text)


def _find_act_start(lines: list[str]) -> int:
    preamble_idx = None
    for i, line in enumerate(lines[:600]):
        if re.match(r"^An?\s+ACT\s+of\s+Parliament\b", line.strip(), re.I):
            preamble_idx = i
            break
    if preamble_idx is not None:
        for j in range(preamble_idx - 1, max(preamble_idx - 30, -1), -1):
            line = lines[j].strip()
            if not line:
                continue
            if _ACT_HEADING_RE.match(line) and line == line.upper():
                return j
            if (
                re.match(r"^[A-Z][A-Z\s,.\-&']+(?:ACT|CODE|BILL)\b", line)
                and len(line) < 150
            ):
                return j
        return preamble_idx
    for i, line in enumerate(lines[:600]):
        s = line.strip()
        if re.match(r"^Part\s+[IVXLCDM]+\s*[-–—:]", s, re.I):
            return i
        if re.match(
            r"^1\.\s+(?:Short\s+title|Citation|Preliminary|Interpretation)\b", s, re.I
        ):
            return i
    return 0


def parse_act_header(content: str) -> dict:
    lines = content.split("\n")
    start = _find_act_start(lines)
    lines = lines[start:]
    title = ""
    act_number = ""
    metadata: list[dict] = []
    preamble = ""
    body_start = 0
    i = 0
    while i < len(lines):
        raw = lines[i]
        stripped = raw.strip()
        if not stripped:
            i += 1
            continue
        m = _ACT_HEADING_RE.match(stripped)
        if m and stripped == stripped.upper() and len(stripped) < 250:
            title = _clean(m.group(1))
            act_number = _clean(m.group(2))
            i += 1
            continue
        if (
            not title
            and stripped == stripped.upper()
            and len(stripped) < 200
            and any(w in stripped for w in ("ACT", "CODE", "CONSTITUTION", "BILL"))
        ):
            title = stripped
            i += 1
            continue
        if not act_number and re.match(
            r"^(?:NO\.?\s*\d+\s+OF\s+\d{4}|CAP\.?\s*\d+[A-Z]?)$", stripped, re.I
        ):
            act_number = stripped
            i += 1
            continue
        mm = _META_LINE_RE.match(stripped)
        if mm:
            metadata.append(
                {"label": _clean(mm.group(1)), "value": _clean(mm.group(2)).strip(" :")}
            )
            i += 1
            continue
        if re.match(r"^An?\s+ACT\s+of\s+Parliament\b", stripped, re.I):
            parts = [stripped]
            j = i + 1
            while j < len(lines):
                nxt = lines[j].strip()
                if not nxt:
                    j += 1
                    continue
                if re.match(
                    r"^(?:Part\s+[IVXLCDM]|\d{1,3}[A-Z]?\.\s+[A-Z])", nxt, re.I
                ):
                    break
                parts.append(nxt)
                j += 1
            preamble = _clean(" ".join(parts))
            body_start = j
            break
        if re.match(r"^(?:Part\s+[IVXLCDM]|\d{1,3}[A-Z]?\.\s+[A-Z])", stripped, re.I):
            body_start = i
            break
        i += 1
    else:
        body_start = i
    return {
        "title": title,
        "act_number": act_number,
        "metadata": metadata,
        "preamble": preamble,
        "body_start": body_start,
        "remaining_lines": lines[body_start:],
    }


def _marker_split(text: str) -> list[tuple[str, str]]:
    if not text:
        return []
    pat = re.compile(r"(?:^|(?<=\n\n))\s*(\((?:\d{1,3}|[a-z]{1,3})\))", re.M | re.I)
    hits = list(pat.finditer(text))
    if not hits:
        return [("", text.strip())]
    out: list[tuple[str, str]] = []
    if hits[0].start() > 0:
        lead = text[: hits[0].start()].strip()
        if lead:
            out.append(("", lead))
    for i, m in enumerate(hits):
        end = hits[i + 1].start() if i + 1 < len(hits) else len(text)
        out.append((m.group(1), text[m.end() : end].strip()))
    return out


def _merge_statute_blocks(blocks: list[str]) -> list[str]:
    merged: list[str] = []
    i = 0
    while i < len(blocks):
        b = blocks[i]
        if re.match(r"^\d{1,3}[A-Z]?\.\s*$", b) and i + 1 < len(blocks):
            merged.append(f"{b} {blocks[i + 1]}")
            i += 2
            continue
        if re.match(r"^(?:Part|PART)\s+[IVXLCDM]+[A-Z]?\s*$", b) and i + 1 < len(
            blocks
        ):
            merged.append(f"{b} — {blocks[i + 1]}")
            i += 2
            continue
        if re.match(r"^\(\d{1,3}\)$|^\([a-z]\)$|^\([ivxlc]{2,}\)$", b) and i + 1 < len(
            blocks
        ):
            merged.append(f"{b} {blocks[i + 1]}")
            i += 2
            continue
        merged.append(b)
        i += 1
    return merged


def _ends_complete(text: str) -> bool:
    t = (text or "").rstrip()
    if not t:
        return True
    return t.endswith((".", "?", "!", ";"))


def _merge_short_blocks(blocks: list[str], min_len: int = 50) -> list[str]:
    merged: list[str] = []
    for b in blocks:
        stripped = b.strip()
        if not stripped:
            continue
        is_pure = bool(_PURE_MARKER_RE.match(stripped))
        is_conj = bool(_CONJUNCTION_RE.match(stripped))
        starts_marker = bool(_STARTS_MARKER_RE.match(stripped))
        starts_numbered = bool(_NUM_START.match(stripped))
        is_short = len(stripped) < min_len
        if merged and (is_pure or is_conj):
            merged[-1] += " " + stripped
            continue
        if merged and is_short and not starts_marker and not starts_numbered:
            merged[-1] += " " + stripped
            continue
        if (
            merged
            and not _ends_complete(merged[-1])
            and len(stripped) < 30
            and not starts_numbered
        ):
            merged[-1] += " " + stripped
            continue
        merged.append(stripped)
    return merged


def _assign_levels(subsections: list[dict]) -> None:
    if not subsections:
        return
    has_digit = False
    has_letter = False
    for s in subsections:
        m = (s.get("marker") or "").strip("().").lower()
        if m.isdigit():
            has_digit = True
        elif len(m) == 1 and m.isalpha() and m != "i":
            has_letter = True
    for i, sub in enumerate(subsections):
        m = (sub.get("marker") or "").strip("().").lower()
        if not m:
            sub["level"] = 1 if has_digit else 0
        elif m.isdigit():
            sub["level"] = 1
        elif m in _ROMAN:
            if has_digit and has_letter:
                sub["level"] = 3
            elif has_digit or has_letter:
                sub["level"] = 2
            else:
                sub["level"] = 1
        else:
            sub["level"] = 2 if has_digit else 1


def _add_subsections(section: dict, text: str) -> None:
    text = re.sub(r"(?<=[—–:.;])\s*\n\s*(?=\()", "\n\n", text)
    for mk, txt in _marker_split(text):
        if not txt:
            continue
        txt = re.sub(r"\s+", " ", txt).strip()
        section["subsections"].append({"level": 0, "marker": mk, "text": txt})


def _find_content_start(blocks: list[str]) -> int:
    if not blocks:
        return 0
    for i, block in enumerate(blocks[:200]):
        b = block.strip()
        m = re.match(r"^1\.\s+(.+)$", b, re.S)
        if not m:
            continue
        rest = m.group(1)
        if "\n" in rest:
            _, _, body = rest.partition("\n")
            if len(body.strip()) > 30:
                return _include_preceding_part(blocks, i)
        if i + 1 < len(blocks):
            nxt = blocks[i + 1].strip()
            if not re.match(r"^\d{1,3}[A-Z]?\.\s", nxt) and len(nxt) > 40:
                return _include_preceding_part(blocks, i)
    return 0


def _include_preceding_part(blocks: list[str], section_idx: int) -> int:
    part_re = re.compile(r"^(?:Part|PART)\s+[IVXLCDM]+", re.I)
    for j in range(section_idx - 1, max(section_idx - 5, -1), -1):
        b = blocks[j].strip()
        if not b:
            continue
        if part_re.match(b):
            return j
        if len(b) > 100:
            break
    return section_idx


def parse_statute_items(body: str) -> list[dict]:
    blocks = [b.strip() for b in re.split(r"\n{2,}", body or "") if b.strip()]
    blocks = _merge_statute_blocks(blocks)
    blocks = _merge_short_blocks(blocks)
    start = _find_content_start(blocks)
    if start > 0:
        blocks = blocks[start:]
    items: list[dict] = []
    current: dict | None = None
    for block in blocks:
        pm = _PART_RE.match(block)
        if pm and len(block) < 300:
            items.append(
                {
                    "type": "part",
                    "number": f"PART {pm.group(1).upper()}",
                    "title": _clean(pm.group(2)).upper(),
                }
            )
            current = None
            continue
        sm = _SECTION_RE.match(block)
        if sm:
            raw_num = sm.group(1)
            try:
                num = int(re.sub(r"[A-Z]", "", raw_num))
            except ValueError:
                num = None
            if num is not None and num < 1000:
                rest = sm.group(2).strip()
                if "\n" in rest:
                    head, _, tail = rest.partition("\n")
                else:
                    m2 = re.match(r"^(.{3,80}?)(?:\.\s+)([A-Z].*)$", rest, re.S)
                    if m2 and len(m2.group(1).split()) <= 12:
                        head, tail = m2.group(1), m2.group(2)
                    else:
                        head, tail = rest, ""
                sec = {
                    "type": "section",
                    "number": raw_num,
                    "title": _clean(head).rstrip("."),
                    "subsections": [],
                }
                if tail.strip():
                    _add_subsections(sec, tail.strip())
                items.append(sec)
                current = sec
                continue
        if current is not None:
            _add_subsections(current, block)
        else:
            items.append({"type": "text", "body": block})
    for it in items:
        if it.get("type") == "section":
            _assign_levels(it.get("subsections", []))
    return items


def statute_toc(items: list[dict]) -> list[dict]:
    toc: list[dict] = []
    current: dict | None = None
    for it in items:
        if it.get("type") == "part":
            current = {
                "type": "part",
                "number": it.get("number", ""),
                "title": it.get("title", ""),
                "sections": [],
            }
            toc.append(current)
        elif it.get("type") == "section":
            if current is None:
                current = {"type": "part", "number": "", "title": "", "sections": []}
                toc.append(current)
            current["sections"].append(
                {
                    "number": str(it.get("number", "")),
                    "title": it.get("title", ""),
                }
            )
    return toc


def build_statute_view(doc: dict) -> dict:
    raw = re.sub(r"[ \t]+", " ", doc.get("body") or "")
    raw = raw.replace("\r\n", "\n").replace("\r", "\n")
    header = parse_act_header(raw)
    body_text = "\n".join(header["remaining_lines"])
    body_text = _normalize_markers(body_text)
    items = parse_statute_items(body_text)
    toc = statute_toc(items)
    has_structure = any(it.get("type") in ("part", "section") for it in items)
    raw_body = "" if has_structure else body_text
    return {
        "kind": "statute",
        "url": doc.get("url", ""),
        "title": header.get("title") or doc.get("title") or "Untitled statute",
        "citation": header.get("act_number") or doc.get("citation") or "",
        "metadata": header.get("metadata", []),
        "preamble": header.get("preamble", ""),
        "items": items,
        "toc": toc,
        "raw_body": raw_body,
        "pdf_only": bool(doc.get("pdf_only")),
        "pdf_url": doc.get("pdf_path") or "",
    }


def public_document(doc: dict) -> dict:
    body = doc.get("body") or ""
    return {
        "id": doc.get("id"),
        "url": doc.get("url", ""),
        "kind": doc.get("kind", "case"),
        "title": doc.get("title") or "Untitled",
        "citation": doc.get("citation", ""),
        "court": doc.get("court", ""),
        "year": doc.get("year", ""),
        "date": doc.get("date", ""),
        "excerpt": _clean(body)[:650],
        "has_body": bool(body.strip()),
        "pdf_only": bool(doc.get("pdf_only")),
        "source": doc.get("source", "Library"),
    }


@app.get("/")
def home():
    return render_template("index.html")


@app.get("/read.html")
def read_page():
    return render_template("read.html")


@app.get("/api/health")
def health():
    with db() as con:
        statutes = con.execute(
            "SELECT COUNT(*) FROM documents WHERE kind='statute' AND body!=''"
        ).fetchone()[0]
        cases = con.execute(
            "SELECT COUNT(*) FROM documents WHERE kind='case' AND body!=''"
        ).fetchone()[0]
    return jsonify(
        {
            "ok": True,
            "statute_docs": statutes,
            "case_docs": cases,
            "constitution_articles": len(load_constitution()),
            "pymupdf": _HAS_FITZ,
        }
    )


@app.get("/api/debug/statute")
def api_debug_statute():
    """Debug: shows raw body, normalized body, and parsed section data."""
    url = canonical_eklr_url(request.args.get("url", ""))
    if not url:
        return jsonify({"error": "Missing url"}), 400
    doc = get_document(url)
    if not doc or not doc.get("body"):
        return jsonify({"error": "Not cached"}), 404

    raw = re.sub(r"[ \t]+", " ", doc["body"])
    raw = raw.replace("\r\n", "\n").replace("\r", "\n")
    header = parse_act_header(raw)
    body_text = "\n".join(header["remaining_lines"])
    normalized = _normalize_markers(body_text)

    # Show first 20 blocks after split
    blocks = [b.strip() for b in re.split(r"\n{2,}", normalized) if b.strip()]

    view = build_statute_view(doc)
    # Find section 2
    sec2 = None
    for it in view.get("items", []):
        if it.get("type") == "section" and it.get("number") == "2":
            sec2 = it
            break

    return jsonify(
        {
            "title": header.get("title"),
            "body_length": len(raw),
            "remaining_lines_count": len(header["remaining_lines"]),
            "normalized_length": len(normalized),
            "block_count": len(blocks),
            "first_10_blocks": blocks[:10],
            "section_2": sec2,
            "total_sections": sum(
                1 for i in view.get("items", []) if i.get("type") == "section"
            ),
        }
    )


@app.get("/api/autocomplete")
def api_autocomplete():
    q = _clean(request.args.get("q", ""))[:80].lower()
    kind = request.args.get("kind", "case")
    if len(q) < 2:
        return jsonify({"suggestions": []})
    with db() as con:
        rows = con.execute(
            "SELECT DISTINCT title FROM documents "
            "WHERE kind=? AND lower(title) LIKE ? LIMIT 12",
            (kind, f"%{q}%"),
        ).fetchall()
    return jsonify({"suggestions": [r["title"] for r in rows]})


@app.post("/api/search")
def api_search():
    payload = request.get_json(silent=True) or {}
    query = _clean(payload.get("query", ""))[:200]
    kind = payload.get("kind", "case")
    if kind not in ("case", "statute"):
        kind = "case"
    if len(query) < 2:
        return jsonify({"error": "Enter at least two characters."}), 400
    with db() as con:
        rows = con.execute(
            "SELECT * FROM documents WHERE kind=? AND "
            "(lower(title) LIKE ? OR lower(citation) LIKE ?) "
            "ORDER BY (body!='') DESC, accessed_at DESC LIMIT ?",
            (kind, f"%{query.lower()}%", f"%{query.lower()}%", MAX_RESULTS),
        ).fetchall()
    cached = [dict(r) for r in rows]
    strong = len(cached) >= 3 and any(
        query.lower() in (d.get("title") or "").lower() for d in cached
    )
    live, live_error = [], None
    if not strong:
        try:
            live, live_error = search_live(query, kind, limit=15)
        except Exception as exc:
            live_error = str(exc)
            log.exception("live search failed")
    merged, seen = [], set()
    for d in live + cached:
        url = d.get("url")
        if url and url not in seen:
            seen.add(url)
            merged.append(d)
    for d in merged[:8]:
        if not d.get("body") and d.get("url"):
            _enqueue_fetch(d["url"], d.get("kind", kind))
    has_thin = any(not d.get("body") for d in merged[:MAX_RESULTS])
    return jsonify(
        {
            "query": query,
            "kind": kind,
            "results": [public_document(d) for d in merged[:MAX_RESULTS]],
            "count": len(merged),
            "online_available": live_error is None,
            "live_error": live_error,
            "has_thin_results": has_thin,
        }
    )


@app.get("/api/library")
def api_library():
    kind = request.args.get("type", "case").lower()
    if kind not in ("case", "statute"):
        kind = "case"
    if kind == "statute":
        manifest = load_acts_manifest()
        with db() as con:
            cached = con.execute(
                "SELECT url, title, citation, body!='' AS has_body "
                "FROM documents WHERE kind='statute'"
            ).fetchall()
        by_norm = {}
        for r in cached:
            by_norm[norm_title(r["title"])] = {
                "url": r["url"],
                "citation": r["citation"] or "",
                "has_body": bool(r["has_body"]),
            }
        docs, seen = [], set()
        for a in manifest:
            key = norm_title(a["title"])
            seen.add(key)
            hit = by_norm.get(key)
            docs.append(
                {
                    "title": a["title"],
                    "citation": a.get("cap") or "",
                    "url": hit["url"] if hit else "",
                    "has_body": bool(hit and hit["has_body"]),
                    "kind": "statute",
                }
            )
        for r in cached:
            key = norm_title(r["title"])
            if key and key not in seen:
                docs.append(
                    {
                        "title": r["title"],
                        "citation": r["citation"] or "",
                        "url": r["url"],
                        "has_body": bool(r["has_body"]),
                        "kind": "statute",
                    }
                )
        docs.sort(key=lambda x: x["title"].lower())
        return jsonify({"documents": docs, "total": len(docs), "kind": "statute"})
    with db() as con:
        rows = con.execute(
            "SELECT * FROM documents WHERE kind='case' AND body!='' "
            "ORDER BY accessed_at DESC, fetched_at DESC LIMIT 500"
        ).fetchall()
    docs = [public_document(dict(r)) for r in rows]
    return jsonify({"documents": docs, "total": len(docs), "kind": "case"})


@app.get("/api/statute/resolve")
def api_statute_resolve():
    title = _clean(request.args.get("title", ""))[:200]
    if not title:
        return jsonify({"error": "Missing title"}), 400
    with db() as con:
        row = con.execute(
            "SELECT url FROM documents WHERE kind='statute' AND lower(title)=lower(?)",
            (title,),
        ).fetchone()
    if row:
        return jsonify({"url": row["url"], "title": title})
    docs, err = search_live(title, "statute", limit=3)
    if docs:
        return jsonify({"url": docs[0]["url"], "title": docs[0]["title"]})
    return jsonify({"error": err or "Not found on EKLR"}), 404


@app.get("/api/constitution/toc")
def api_const_toc():
    return jsonify({"chapters": constitution_toc()})


@app.get("/api/constitution/article/<int:number>")
def api_const_article(number: int):
    for art in load_constitution():
        if art.get("number") == number:
            art = dict(art)
            art["paragraphs"] = constitution_paragraphs(art.get("lines", []))
            return jsonify(art)
    return jsonify({"error": "Article not found"}), 404


@app.get("/api/constitution/search")
def api_const_search():
    q = _clean(request.args.get("q", "")).lower()
    if not q:
        return jsonify({"results": []})
    results = []
    for art in load_constitution():
        text = f"{art.get('title', '')} {' '.join(art.get('lines', []))}".lower()
        if q in text:
            results.append(
                {
                    "number": art["number"],
                    "title": art["title"],
                    "chapter": art.get("chapter"),
                    "part": art.get("part"),
                }
            )
        if len(results) >= 60:
            break
    return jsonify({"results": results})


@app.get("/api/case/structured")
def api_case_structured():
    url = canonical_eklr_url(request.args.get("url", ""))
    if not url:
        return jsonify({"error": "Invalid URL"}), 400
    doc = ensure_document(url, "case")
    if not doc:
        return jsonify({"error": "Could not fetch document"}), 502
    return jsonify(build_case_view(doc))


@app.get("/api/statute/structured")
def api_statute_structured():
    url = canonical_eklr_url(request.args.get("url", ""))
    if not url:
        return jsonify({"error": "Invalid URL"}), 400
    doc = ensure_document(url, "statute")
    if not doc:
        return jsonify({"error": "Could not fetch document"}), 502
    if not doc.get("body"):
        return jsonify(
            {
                "kind": "statute",
                "url": url,
                "title": doc.get("title") or "Untitled statute",
                "pdf_only": True,
                "items": [],
                "toc": [],
            }
        )
    return jsonify(build_statute_view(doc))


@app.errorhandler(HTTPException)
def http_error(err):
    if request.path.startswith("/api/"):
        return jsonify({"error": err.description}), err.code
    return err


@app.errorhandler(Exception)
def unhandled(err):
    log.exception("unhandled")
    if request.path.startswith("/api/"):
        return jsonify({"error": "Internal server error."}), 500
    return "Internal server error.", 500


init_db()
load_constitution()
load_acts_manifest()


def _port_free(host: str, port: int) -> bool:
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.bind((host, port))
            return True
    except OSError:
        return False


if __name__ == "__main__":
    # Render/Railway/Fly set PORT env var — bind to 0.0.0.0 on that exact port.
    # Locally PORT is unset, so we default to 5000 with the port-scan fallback.
    cloud_port = os.getenv("PORT")

    if cloud_port:
        target_host = "0.0.0.0"
        target_port = int(cloud_port)
        log.info("LawDesk (cloud): http://%s:%d  (pymupdf=%s)",
                 target_host, target_port, _HAS_FITZ)
        app.run(host=target_host, port=target_port,
                debug=False, threaded=True, use_reloader=False)
    else:
        target = PORT
        if not _port_free(HOST, PORT):
            for offset in range(1, 21):
                if _port_free(HOST, PORT + offset):
                    target = PORT + offset
                    break
            else:
                log.error("No free port in %d..%d", PORT, PORT + 20)
                sys.exit(1)
            log.warning("Port %d busy — using %d. Open http://%s:%d",
                        PORT, target, HOST, target)
        log.info("LawDesk: http://%s:%d  (pymupdf=%s)", HOST, target, _HAS_FITZ)
        app.run(host=HOST, port=target, debug=False, threaded=True,
                use_reloader=False)

from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import sqlite3
import threading
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import quote, urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from flask import (
    Flask, Response, jsonify, render_template, request, send_file, stream_with_context,
)
from werkzeug.exceptions import HTTPException

try:
    import fitz  # PyMuPDF
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
FETCH_WORKERS = max(2, min(int(os.getenv("EKLR_FETCH_WORKERS", "24")), 48))

OFFICIAL_HOSTS = {
    "kenyalaw.org", "www.kenyalaw.org", "new.kenyalaw.org", "old.kenyalaw.org",
    "judiciary.go.ke", "www.judiciary.go.ke",
    "parliament.go.ke", "www.parliament.go.ke",
}

USER_AGENT = "Library/6.0 (public legal research)"
PAGE_CACHE_SECONDS = 30 * 24 * 3600
HTTP_TIMEOUT = (5, 30)
ONLINE_CACHE_SECONDS = 30
SCHEMA_VERSIONS = {"case": 2, "statute": 10}

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("library")

if not _HAS_FITZ:
    log.warning("PyMuPDF not installed — install with: pip install PyMuPDF")

app = Flask(__name__, template_folder=str(TEMPLATE_DIR))
app.config["JSON_SORT_KEYS"] = False
app.config["JSONIFY_PRETTYPRINT_REGULAR"] = False
app.config["SEND_FILE_MAX_AGE_DEFAULT"] = 86400

local = threading.local()
FETCH_POOL = ThreadPoolExecutor(max_workers=FETCH_WORKERS, thread_name_prefix="fetch")
BACKGROUND_POOL = ThreadPoolExecutor(max_workers=4, thread_name_prefix="bg")

_online_cache: dict = {"value": None, "checked": 0.0}
_online_lock = threading.Lock()

bootstrap_lock = threading.Lock()
bootstrap_started = False
bootstrap_state: dict = {
    "running": False, "started_at": 0.0, "finished_at": 0.0,
    "kind": None, "total": 0, "completed": 0, "failed": 0, "detail": "",
}
bootstrap_state_lock = threading.Lock()


# ============================================================
# ACTS MANIFEST
# ============================================================

ACTS_MANIFEST_JSON = r"""[
  {"title": "Access to Information Act", "cap": "Cap. 7M", "year": 2016},
  {"title": "Accountants Act", "cap": "Cap. 531", "year": null},
  {"title": "Advocates Act", "cap": "Cap. 16", "year": null},
  {"title": "Affordable Housing Act", "cap": "Act No. 2 of 2024", "year": 2024},
  {"title": "African Development Bank Act", "cap": "Cap. 492", "year": null},
  {"title": "African Re-insurance Corporation (Mandatory Re-insurance Cessions) Act", "cap": "Cap. 487B", "year": null},
  {"title": "Age of Majority Act", "cap": "Cap. 33", "year": null},
  {"title": "Agricultural Development Corporation Act", "cap": "Cap. 444", "year": null},
  {"title": "Agricultural Finance Corporation Act", "cap": "Cap. 323", "year": null},
  {"title": "Agriculture and Food Authority Act", "cap": "Cap. 317", "year": null},
  {"title": "Air Passenger Service Charge Act", "cap": "Cap. 475", "year": null},
  {"title": "Anti-Counterfeit Act", "cap": "No. 13 of 2008", "year": 2008},
  {"title": "Anti-Doping Act", "cap": null, "year": null},
  {"title": "Appellate Jurisdiction Act", "cap": null, "year": null},
  {"title": "Appropriation Act", "cap": "Act No. 7 of 2021", "year": 2021},
  {"title": "Arbitration Act", "cap": "Cap. 49", "year": 1995},
  {"title": "Architects and Quantity Surveyors Act", "cap": "Cap. 525", "year": null},
  {"title": "Asian Officers' Family Pensions Act", "cap": null, "year": null},
  {"title": "Assumption of the Office of Governor Act", "cap": null, "year": null},
  {"title": "Assumption of the Office of President Act", "cap": null, "year": null},
  {"title": "Auctioneers Act", "cap": "Cap. 526", "year": null},
  {"title": "Bank of Baroda (Kenya) Limited Act", "cap": null, "year": null},
  {"title": "Banking Act", "cap": "Cap. 488", "year": null},
  {"title": "Bankruptcy Act", "cap": "Cap. 53", "year": null},
  {"title": "Basic Education Act", "cap": "No. 14 of 2013", "year": 2013},
  {"title": "Betting, Lotteries and Gaming Act", "cap": "Cap. 131", "year": null},
  {"title": "Bills of Exchange Act", "cap": "Cap. 27", "year": null},
  {"title": "Building Societies Act", "cap": "Cap. 489", "year": null},
  {"title": "Building Surveyors Act", "cap": "Cap. 541", "year": null},
  {"title": "Capital Markets Act", "cap": "Cap. 485A", "year": null},
  {"title": "Central Bank of Kenya Act", "cap": "Cap. 491", "year": null},
  {"title": "Chattels Transfer Act", "cap": "Cap. 28", "year": null},
  {"title": "Cheques Act", "cap": "Cap. 35", "year": null},
  {"title": "Chiefs' Act", "cap": "Cap. 128", "year": null},
  {"title": "Children Act", "cap": "No. 8 of 2001", "year": 2001},
  {"title": "Civil Aviation Act", "cap": "Cap. 394", "year": null},
  {"title": "Civil Procedure Act", "cap": "Cap. 21", "year": null},
  {"title": "Climate Change Act", "cap": "No. 11 of 2016", "year": 2016},
  {"title": "Clinical Officers (Training, Registration and Licensing) Act", "cap": "Cap. 253E", "year": null},
  {"title": "Coast Development Authority Act", "cap": "Cap. 449", "year": null},
  {"title": "Coffee Act", "cap": "Act No. 8 of 2026", "year": 2026},
  {"title": "Companies Act", "cap": "No. 17 of 2015", "year": 2015},
  {"title": "Competition Act", "cap": "No. 12 of 2010", "year": 2010},
  {"title": "Computer Misuse and Cybercrimes Act", "cap": "No. 5 of 2018", "year": 2018},
  {"title": "Consumer Protection Act", "cap": "No. 46 of 2012", "year": 2012},
  {"title": "Contracts in Restraint of Trade Act", "cap": "Cap. 24", "year": null},
  {"title": "County Governments Act", "cap": "No. 17 of 2012", "year": 2012},
  {"title": "Criminal Procedure Code", "cap": "Cap. 75", "year": null},
  {"title": "Dairy Industry Act", "cap": "Cap. 336", "year": null},
  {"title": "Data Protection Act", "cap": "No. 24 of 2019", "year": 2019},
  {"title": "Debts (Summary Recovery) Act", "cap": "Cap. 44", "year": null},
  {"title": "Deeds of Arrangement Act", "cap": "Cap. 54", "year": null},
  {"title": "East African Community Mediation Agreement Act", "cap": null, "year": null},
  {"title": "East African Development Bank Act", "cap": "Cap. 493", "year": null},
  {"title": "Elections Act", "cap": "No. 24 of 2011", "year": 2011},
  {"title": "Employment Act", "cap": "Cap. 226", "year": 2007},
  {"title": "Energy Act", "cap": "No. 1 of 2019", "year": 2019},
  {"title": "Ethics and Anti-Corruption Act", "cap": "No. 22 of 2011", "year": 2011},
  {"title": "Exchequer and Audit Act", "cap": "Cap. 412", "year": null},
  {"title": "Excise Duty Act", "cap": "No. 23 of 2015", "year": 2015},
  {"title": "Explosives Act", "cap": "Cap. 115", "year": null},
  {"title": "Export Processing Zones Act", "cap": "Cap. 517", "year": null},
  {"title": "Extradition (Commonwealth Countries) Act", "cap": "Cap. 76", "year": null},
  {"title": "Extradition (Contiguous and Foreign Countries) Act", "cap": "Cap. 77", "year": null},
  {"title": "Gambling Control Act", "cap": "No. 14 of 2025", "year": 2025, "aliases": ["Gambling Control Act, 2025"]},
  {"title": "Girl Guides Act", "cap": "Cap. 220", "year": null},
  {"title": "Gold Mines Development Loans Act", "cap": "Cap. 311", "year": null},
  {"title": "Government Accommodation Act", "cap": "Cap. 129", "year": null},
  {"title": "Government Contracts Act", "cap": "Cap. 25", "year": null},
  {"title": "Government Owned Enterprises Act", "cap": "Act No. 25 of 2025", "year": 2025},
  {"title": "Government Proceedings Act", "cap": "Cap. 40", "year": null},
  {"title": "Government Securities Act", "cap": "Cap. 421", "year": null},
  {"title": "Guarantee (High Commission Posts and Telecommunications Loan) (No. 1) Act", "cap": "Cap. 450", "year": null},
  {"title": "Guarantee (High Commission Posts and Telecommunications Loan) (No. 2) Act", "cap": "Cap. 451", "year": null},
  {"title": "Guarantee (High Commission Posts and Telecommunications Loan) (No. 3) Act", "cap": "Cap. 452", "year": null},
  {"title": "Guarantee (High Commission Railways and Harbours Loan) (No. 1) Act", "cap": "Cap. 455", "year": null},
  {"title": "Guarantee (High Commission Railways and Harbours Loan) (No. 3) Act", "cap": "Cap. 458", "year": null},
  {"title": "Guarantee (High Commission Railways and Harbours Loan) (No. 4) Act", "cap": "Cap. 459", "year": null},
  {"title": "Guarantee (High Commission Railways and Harbours Loan) (No. 5) Act", "cap": "Cap. 460", "year": null},
  {"title": "Guarantee (High Commission Railways and Harbours Loans) (No. 2) Act", "cap": "Cap. 456", "year": null},
  {"title": "Guarantee (High Commission Railways and Harbours Loans) (Supplementary Provisions) Act", "cap": "Cap. 457", "year": null},
  {"title": "Guarantee (House Purchase) Act", "cap": "Cap. 462", "year": null},
  {"title": "Health Act", "cap": "Cap. 241", "year": null},
  {"title": "Health Records and Information Managers Act", "cap": "Cap. 539", "year": null},
  {"title": "Hide, Skin and Leather Trade Act", "cap": "Cap. 359", "year": null},
  {"title": "High Court (Organization and Administration) Act", "cap": "Cap. 8C", "year": null},
  {"title": "Higher Education Loans Board Act", "cap": "Cap. 213", "year": null},
  {"title": "Hire-Purchase Act", "cap": "Cap. 507", "year": null},
  {"title": "HIV and AIDS Prevention and Control Act", "cap": "Cap. 246A", "year": null},
  {"title": "Human Resource Management Professionals Act", "cap": "Cap. 538", "year": null},
  {"title": "Human Tissue Act", "cap": "Cap. 252", "year": null},
  {"title": "Hydrologists Act", "cap": "Cap. 372B", "year": null},
  {"title": "Income Tax Act", "cap": "Cap. 470", "year": null},
  {"title": "Independent Electoral and Boundaries Commission Act", "cap": "No. 9 of 2011", "year": 2011},
  {"title": "Industrial Training Act", "cap": "Cap. 237", "year": null},
  {"title": "Insurance Act", "cap": "Cap. 487", "year": null},
  {"title": "Intergovernmental Relations Act", "cap": "No. 2 of 2012", "year": 2012},
  {"title": "Judiciary Act", "cap": "Cap. 8", "year": null},
  {"title": "Kadhis' Courts Act", "cap": "Cap. 11", "year": null},
  {"title": "Kenya Agricultural and Livestock Research Act", "cap": "No. 17 of 2013", "year": 2013},
  {"title": "Kenya Airports Authority Act", "cap": "Cap. 395", "year": null},
  {"title": "Kenya Broadcasting Corporation Act", "cap": "Cap. 221", "year": null},
  {"title": "Kenya Citizens and Foreign Nationals Management Service Act", "cap": "No. 31 of 2011", "year": 2011},
  {"title": "Kenya Citizenship and Immigration Act", "cap": "No. 12 of 2011", "year": 2011},
  {"title": "Labour Institutions Act", "cap": "No. 12 of 2007", "year": 2007},
  {"title": "Land Act", "cap": "No. 6 of 2012", "year": 2012},
  {"title": "Land Control Act", "cap": "Cap. 302", "year": 1967},
  {"title": "Land Registration Act", "cap": "No. 3 of 2012", "year": 2012},
  {"title": "Law of Contract Act", "cap": "Cap. 23", "year": null},
  {"title": "Law of Succession Act", "cap": "Cap. 160", "year": null},
  {"title": "Law Society of Kenya Act", "cap": "Cap. 18", "year": null},
  {"title": "Leadership and Integrity Act", "cap": "No. 19 of 2012", "year": 2012},
  {"title": "Legal Aid Act", "cap": "No. 6 of 2016", "year": 2016},
  {"title": "Legal Education Act", "cap": "No. 27 of 2012", "year": 2012},
  {"title": "Legitimacy Act", "cap": "Cap. 145", "year": null},
  {"title": "Limited Liability Partnership Act", "cap": "No. 6 of 2011", "year": 2011},
  {"title": "Magistrates' Courts Act", "cap": "Cap. 10", "year": null},
  {"title": "Malaria Prevention Act", "cap": "Cap. 246", "year": null},
  {"title": "Marriage Act", "cap": "No. 4 of 2014", "year": 2014},
  {"title": "Mining Act", "cap": "No. 12 of 2016", "year": 2016},
  {"title": "Nairobi Centre for International Arbitration Act", "cap": "No. 15 of 2013", "year": 2013},
  {"title": "National Council for Law Reporting Act", "cap": "No. 19 of 1994", "year": 1994},
  {"title": "National Payment Systems Act", "cap": "No. 39 of 2011", "year": 2011},
  {"title": "Oaths and Statutory Declarations Act", "cap": "Cap. 15", "year": null},
  {"title": "Parliamentary Service Act", "cap": "No. 22 of 2019", "year": 2019},
  {"title": "Petition to Parliament (Procedure) Act", "cap": "No. 22 of 2012", "year": 2012},
  {"title": "Petroleum Act", "cap": "No. 2 of 2019", "year": 2019},
  {"title": "Political Parties Act", "cap": "No. 11 of 2011", "year": 2011},
  {"title": "Prevention of Corruption and Economic Crimes Act", "cap": "No. 3 of 2003", "year": 2003},
  {"title": "Prevention of Organised Crimes Act", "cap": "No. 6 of 2010", "year": 2010},
  {"title": "Public Appointments (Parliamentary Approval) Act", "cap": "No. 33 of 2011", "year": 2011},
  {"title": "Public Finance Management Act", "cap": "No. 18 of 2012", "year": 2012},
  {"title": "Public Health Act", "cap": "Cap. 242", "year": null},
  {"title": "Public Private Partnerships Act", "cap": "No. 15 of 2013", "year": 2013},
  {"title": "Public Procurement and Asset Disposal Act", "cap": "No. 33 of 2015", "year": 2015},
  {"title": "Public Service (Values and Principles) Act", "cap": "No. 1A of 2015", "year": 2015},
  {"title": "Registration of Persons Act", "cap": "Cap. 107", "year": null},
  {"title": "Registration of Titles Act", "cap": "Cap. 281", "year": null},
  {"title": "Regulation of Wages and Conditions of Employment Act", "cap": "Cap. 229", "year": null},
  {"title": "Retirement Benefits Act", "cap": "No. 3 of 1997", "year": 1997},
  {"title": "Roads Act", "cap": "Cap. 399", "year": null},
  {"title": "Scrap Metal Act", "cap": "No. 1 of 2015", "year": 2015},
  {"title": "Sexual Offences Act", "cap": "No. 3 of 2006", "year": 2006},
  {"title": "Standards Act", "cap": "Cap. 496", "year": null},
  {"title": "Stamp Duty Act", "cap": "Cap. 480", "year": null},
  {"title": "State Corporations Act", "cap": "Cap. 446", "year": null},
  {"title": "Statutory Instruments Act", "cap": "No. 23 of 2013", "year": 2013},
  {"title": "Tax Procedures Act", "cap": "No. 29 of 2015", "year": 2015},
  {"title": "Tea Act", "cap": "No. 23 of 2020", "year": 2020},
  {"title": "Trade Marks Act", "cap": "Cap. 506", "year": 1955},
  {"title": "Trade Unions Act", "cap": "Cap. 233", "year": null},
  {"title": "Traffic Act", "cap": "Cap. 403", "year": null},
  {"title": "Transfer of Property Act", "cap": "Cap. 285", "year": null},
  {"title": "Treaty Making and Ratification Act", "cap": "No. 45 of 2012", "year": 2012},
  {"title": "Truth, Justice and Reconciliation Act", "cap": "No. 6 of 2008", "year": 2008},
  {"title": "Universities Act", "cap": "No. 42 of 2012", "year": 2012},
  {"title": "Urban Areas and Cities Act", "cap": "No. 13 of 2011", "year": 2011},
  {"title": "Value Added Tax Act", "cap": "No. 35 of 2013", "year": 2013},
  {"title": "Vetting of Judges and Magistrates Act", "cap": "No. 2 of 2011", "year": 2011},
  {"title": "Water Act", "cap": "No. 43 of 2016", "year": 2016},
  {"title": "Work Injury Benefits Act", "cap": "No. 13 of 2007", "year": 2007}
]"""


def load_acts_manifest() -> list[dict]:
    if not ACTS_JSON_PATH.exists():
        try:
            ACTS_JSON_PATH.write_text(ACTS_MANIFEST_JSON, encoding="utf-8")
        except Exception as exc:
            log.warning("Could not write acts.json: %s", exc)
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
        log.warning("Could not load acts.json: %s", exc)
        return []


# ============================================================
# KENYA LAW CLIENT
# ============================================================

class KenyaLaw:
    BASE = "https://new.kenyalaw.org"
    LEGISLATION_INDEX = "/legislation/"
    JUDGMENTS_INDEX = "/judgments/"
    SEARCH_PATH = "/search/"

    def __init__(self):
        self._session = requests.Session()
        self._session.headers.update({
            "User-Agent": USER_AGENT,
            "Accept": "application/json, text/html;q=0.9, application/xml;q=0.8, */*;q=0.5",
        })

    def _get(self, url, params=None, headers=None, timeout=(5, 30)):
        try:
            r = self._session.get(url, params=params, headers=headers, timeout=timeout)
            r.raise_for_status()
            return r
        except Exception as exc:
            log.debug("GET %s → %s", url, exc)
            return None

    @staticmethod
    def _parse_links(html: str, prefix: str) -> list[dict]:
        soup = BeautifulSoup(html, "html.parser")
        out, seen = [], set()
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if not href.startswith(prefix):
                continue
            title = clean(a.get_text(" ", strip=True))
            if not title or len(title) < 4:
                continue
            if href in seen:
                continue
            seen.add(href)
            out.append({
                "title": title, "href": href,
                "url": (KenyaLaw.BASE + href) if href.startswith("/") else href,
            })
        return out

    def crawl_legislation(self, max_pages: int = 200) -> list[dict]:
        out, seen = [], set()
        for page in range(1, max_pages + 1):
            r = self._get(self.BASE + self.LEGISLATION_INDEX, params={"page": page})
            if not r:
                break
            items = self._parse_links(r.text, "/akn/ke/act/")
            new = [it for it in items if it["href"] not in seen]
            if not new:
                break
            for it in new:
                seen.add(it["href"])
                out.append(it)
            if len(items) < 5:
                break
        return out

    def crawl_judgments(self, max_pages: int = 40) -> list[dict]:
        out, seen = [], set()
        for page in range(1, max_pages + 1):
            r = self._get(self.BASE + self.JUDGMENTS_INDEX, params={"page": page})
            if not r:
                break
            items = self._parse_links(r.text, "/akn/ke/judgment/")
            new = [it for it in items if it["href"] not in seen]
            if not new:
                break
            for it in new:
                seen.add(it["href"])
                out.append(it)
            if len(items) < 5:
                break
        return out

    def search(self, q: str, kind: str | None = None, max_results: int = 20) -> list[dict]:
        if not q:
            return []
        params = {"q": q}
        if kind == "act":
            params["type"] = "legislation"
            prefix = "/akn/ke/act/"
        elif kind == "judgment":
            params["type"] = "judgment"
            prefix = "/akn/ke/judgment/"
        else:
            prefix = "/akn/ke/"
        r = self._get(self.BASE + self.SEARCH_PATH, params=params)
        if not r:
            return []
        return self._parse_links(r.text, prefix)[:max_results]

    def fetch_akn(self, url: str) -> dict | None:
        for suffix in (".json", ""):
            try_url = url if url.endswith(suffix) else url + suffix
            headers = {"Accept": "application/json"} if not suffix else None
            r = self._get(try_url, headers=headers, timeout=(5, 25))
            if r and "json" in (r.headers.get("Content-Type") or "").lower():
                try:
                    data = r.json()
                    if isinstance(data, dict):
                        return {"format": "json", "content": data, "url": r.url}
                except Exception:
                    pass
        r = self._get(url, headers={"Accept": "text/html"}, timeout=(5, 25))
        if r and "html" in (r.headers.get("Content-Type") or "").lower():
            return {"format": "html", "content": r.text, "url": r.url}
        for suffix in ("/source", ".xml"):
            r = self._get(url + suffix, timeout=(5, 25))
            if r:
                txt = r.text or ""
                if "xml" in (r.headers.get("Content-Type") or "").lower() or txt.startswith("<"):
                    return {"format": "xml", "content": txt, "url": r.url}
        return None

    def fetch_pdf_text(self, url: str) -> str:
        if not _HAS_FITZ:
            return ""
        for suffix in ("/download", ".pdf", ""):
            try_url = url if url.endswith(suffix) else url + suffix
            try:
                r = self._session.get(try_url, timeout=(5, 60), allow_redirects=True)
                if r.ok and r.content and r.content[:5] == b"%PDF-":
                    text = extract_pdf_text(r.content)
                    if text:
                        return text
            except Exception:
                pass
        return ""

    @staticmethod
    def norm_title(s: str) -> str:
        return re.sub(r"[^a-z0-9]+", " ", (s or "").lower()).strip()


KL = KenyaLaw()


# ============================================================
# URL CLASSIFIERS
# ============================================================

_CASE_INDIVIDUAL_RE = re.compile(
    r"/caselaw/cases/view/\d+|/akn/ke/judgment/[a-z]+/\d{4}/\d+", re.I,
)
_ACT_URL_RE = re.compile(r"(?:/akn/ke/act/|/kl/acts?(?:/|$)|/legislation/)", re.I)


def is_individual_case_url(url: str) -> bool:
    return bool(url) and bool(_CASE_INDIVIDUAL_RE.search(url))


def is_act_url(url: str) -> bool:
    if not url:
        return False
    if is_individual_case_url(url):
        return False
    if url.lower().endswith(".pdf") or ".pdf?" in url.lower():
        return False
    return bool(_ACT_URL_RE.search(url))


def determine_kind(url: str, hint: str | None = None) -> str:
    if is_individual_case_url(url):
        return "case"
    if is_act_url(url):
        return "statute"
    if "constitution of kenya" in (url or "").lower():
        return "constitution"
    if hint in ("constitution", "statute", "case"):
        return hint
    return "case"


# ============================================================
# CHROME / ACT DETECTION
# ============================================================

_CHROME_MARKERS = (
    "share this document", "report a problem", "download pdf",
    "download original enactment", "copy citation", "document detail",
    "related documents", "this feature is not currently available",
    "to the top",
)


def looks_like_chrome(body: str) -> bool:
    if not body:
        return False
    lowered = body.lower()
    return sum(1 for m in _CHROME_MARKERS if m in lowered) >= 2


def looks_like_act_text(body: str) -> bool:
    if not body or len(body) < 500:
        return False
    if looks_like_chrome(body):
        return False
    has_sections = bool(re.search(r"\b\d{1,3}[A-Z]?\.\s+[A-Z]", body))
    has_phrases = any(w in body.lower() for w in (
        "short title", "this act may be cited", "an act of parliament",
        "part i", "part 1", "interpretation", "enacted by",
    ))
    return has_sections or has_phrases or len(body) > 5000


# ============================================================
# MEMORY INDEX
# ============================================================


class MemoryIndex:
    _TOKEN_RE = re.compile(r"[a-z0-9]{2,}")

    def __init__(self, name: str):
        self.name = name
        self._lock = threading.RLock()
        self.tokens: dict[str, set[int]] = defaultdict(set)
        self.prefixes: dict[str, set[int]] = defaultdict(set)
        self.docs: dict[int, dict] = {}
        self.citations: dict[str, int] = {}
        self.bodies: dict[int, str] = {}
        self.vocabulary: set[str] = set()

    @classmethod
    def _tokenize(cls, text: str) -> list[str]:
        return cls._TOKEN_RE.findall((text or "").lower())

    @classmethod
    def _norm_cite(cls, text: str) -> str:
        return re.sub(r"\s+", " ", (text or "").strip().lower()) if text else ""

    def index_document(self, doc_id, title, citation, body, url,
                       court="", year="", aliases_list=None):
        with self._lock:
            aliases_text = " ".join(str(a) for a in (aliases_list or []))
            all_text = " ".join([
                (title or "").lower(), (citation or "").lower(),
                (court or "").lower(), (year or "").lower(),
                aliases_text.lower(),
                (body or "")[:20000].lower(),
            ])
            toks = set(self._tokenize(all_text))
            self.docs[doc_id] = {
                "id": doc_id, "title": title or "Untitled",
                "citation": citation or "", "url": url or "",
                "court": court or "", "year": year or "", "kind": self.name,
                "aliases_list": aliases_list or [],
            }
            for t in toks:
                self.tokens[t].add(doc_id)
                for i in range(2, min(len(t), 20) + 1):
                    self.prefixes[t[:i]].add(doc_id)
            if citation:
                self.citations[self._norm_cite(citation.lower())] = doc_id
            for a in (aliases_list or []):
                k = self._norm_cite(str(a).lower())
                if k and k not in self.citations:
                    self.citations[k] = doc_id
            self.bodies[doc_id] = (body or "").lower()
            self.vocabulary.update(toks)

    def bulk_load(self, rows):
        with self._lock:
            self.tokens.clear(); self.prefixes.clear(); self.docs.clear()
            self.citations.clear(); self.bodies.clear(); self.vocabulary.clear()
            for r in rows:
                self.index_document(
                    r["id"], r.get("title", ""), r.get("citation", ""),
                    r.get("body", ""), r.get("url", ""),
                    r.get("court", ""), r.get("year", ""),
                    aliases_list=r.get("aliases_list") or [],
                )

    def remove_document(self, doc_id):
        with self._lock:
            self.docs.pop(doc_id, None)
            self.bodies.pop(doc_id, None)
            for t in list(self.tokens.keys()):
                if doc_id in self.tokens[t]:
                    self.tokens[t].discard(doc_id)
                    if not self.tokens[t]:
                        del self.tokens[t]

    def search(self, query: str, limit: int = 60) -> list[dict]:
        q = (query or "").strip().lower()
        if not q:
            return []
        with self._lock:
            norm = self._norm_cite(q)
            if norm in self.citations:
                did = self.citations[norm]
                d = self.docs.get(did)
                if d:
                    return [dict(d, score=1000.0)]
            qtoks = self._tokenize(q)
            if not qtoks:
                matches = [t for t in self.vocabulary if t.startswith(q)][:10]
                if not matches:
                    return []
                qtoks = matches
            sets = [self.tokens.get(t, set()) for t in qtoks]
            sets = [s for s in sets if s]
            if not sets:
                candidates = self.prefixes.get(q, set())
                if not candidates:
                    return []
            else:
                candidates = set.intersection(*sets) if len(sets) > 1 else sets[0]
                if not candidates:
                    candidates = set.union(*sets)
            qset = set(qtoks)
            scored = []
            for did in candidates:
                d = self.docs.get(did)
                if not d:
                    continue
                tl = d["title"].lower(); cl = d["citation"].lower()
                al = " ".join(d.get("aliases_list") or []).lower()
                body = self.bodies.get(did, "")
                score = 0.0
                for t in qset:
                    if t in tl: score += 30
                    if t in cl: score += 20
                    if t in al: score += 25
                    if t in body: score += 2
                if q in tl: score += 200
                if q in cl: score += 150
                if q in al: score += 180
                scored.append((score, d))
            scored.sort(key=lambda x: x[0], reverse=True)
            return [dict(d, score=round(s, 2)) for s, d in scored[:limit]]

    def autocomplete(self, prefix: str, limit: int = 12) -> list[str]:
        p = (prefix or "").strip().lower()
        if len(p) < 2:
            return []
        with self._lock:
            hits = []
            for d in self.docs.values():
                if p in d["title"].lower():
                    hits.append(d["title"])
                    if len(hits) >= limit:
                        break
            return hits


STATUTE_INDEX = MemoryIndex("statute")
CONSTITUTION_INDEX = MemoryIndex("constitution")
CASE_INDEX = MemoryIndex("case")


def _index_for_kind(kind: str) -> MemoryIndex | None:
    return {"statute": STATUTE_INDEX, "constitution": CONSTITUTION_INDEX,
            "case": CASE_INDEX}.get(kind)


def _all_indexes() -> list[MemoryIndex]:
    return [CONSTITUTION_INDEX, STATUTE_INDEX, CASE_INDEX]


# ============================================================
# ONLINE CHECK
# ============================================================


def check_online(timeout: float = 2.0, force: bool = False) -> bool:
    now = time.time()
    with _online_lock:
        if (not force and _online_cache["value"] is not None
                and now - _online_cache["checked"] < ONLINE_CACHE_SECONDS):
            return _online_cache["value"]
    ok = False
    try:
        r = requests.head("https://new.kenyalaw.org", timeout=timeout,
                          allow_redirects=True, headers={"User-Agent": USER_AGENT})
        ok = r.status_code < 500
    except Exception:
        ok = False
    with _online_lock:
        _online_cache["value"] = ok
        _online_cache["checked"] = now
    return ok


# ============================================================
# DATABASE
# ============================================================


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
                pdf_url TEXT NOT NULL DEFAULT '',
                pdf_path TEXT NOT NULL DEFAULT '',
                pdf_status TEXT NOT NULL DEFAULT 'not_found',
                aliases TEXT NOT NULL DEFAULT '[]',
                source TEXT NOT NULL DEFAULT 'Library',
                fetched_at REAL NOT NULL DEFAULT 0,
                created_at REAL NOT NULL DEFAULT (unixepoch()),
                accessed_at REAL NOT NULL DEFAULT 0,
                relevance REAL NOT NULL DEFAULT 0
            )
        """)
        # Add aliases column to existing DBs
        try:
            cols = {r[1] for r in con.execute("PRAGMA table_info(documents)").fetchall()}
            if "aliases" not in cols:
                con.execute("ALTER TABLE documents ADD COLUMN aliases TEXT NOT NULL DEFAULT '[]'")
        except Exception:
            pass
        con.execute("CREATE INDEX IF NOT EXISTS idx_documents_kind ON documents(kind)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_documents_citation ON documents(citation)")
        con.execute("""
            CREATE TABLE IF NOT EXISTS search_cache (
                query TEXT PRIMARY KEY,
                results TEXT NOT NULL,
                created_at REAL NOT NULL
            )
        """)


def migrate_kinds() -> int:
    fixed = 0
    with db() as con:
        rows = con.execute("SELECT id, url, kind FROM documents").fetchall()
        for r in rows:
            want = determine_kind(r["url"], r["kind"])
            if r["kind"] != want:
                con.execute("UPDATE documents SET kind=? WHERE id=?", (want, r["id"]))
                fixed += 1
    if fixed:
        log.info("Migrated %d rows to correct kind", fixed)
    return fixed


def purge_chrome_statutes() -> int:
    purged = 0
    with db() as con:
        rows = con.execute(
            "SELECT id, url, body, pdf_path FROM documents "
            "WHERE kind='statute' AND body != ''"
        ).fetchall()
        for r in rows:
            body = r["body"] or ""
            if looks_like_chrome(body) or (
                len(body) > 200 and not looks_like_act_text(body)
            ):
                if r["pdf_path"]:
                    try:
                        Path(r["pdf_path"]).unlink(missing_ok=True)
                        Path(r["pdf_path"]).with_suffix(".url").unlink(missing_ok=True)
                    except Exception:
                        pass
                con.execute(
                    "UPDATE documents SET body='', pdf_status='not_found', pdf_path='' "
                    "WHERE id=?", (r["id"],),
                )
                purged += 1
    if purged:
        log.info("Purged %d chrome-only statutes for refetch", purged)
    return purged


def rebuild_memory_indexes():
    with db() as con:
        rows = con.execute(
            "SELECT id,url,kind,title,citation,court,year,body,aliases FROM documents"
        ).fetchall()
    by_kind = {"constitution": [], "statute": [], "case": []}
    for r in rows:
        d = dict(r)
        try:
            d["aliases_list"] = json.loads(d.get("aliases") or "[]")
        except Exception:
            d["aliases_list"] = []
        k = d.get("kind") or "case"
        if k in by_kind:
            by_kind[k].append(d)
    CONSTITUTION_INDEX.bulk_load(by_kind["constitution"])
    STATUTE_INDEX.bulk_load(by_kind["statute"])
    CASE_INDEX.bulk_load(by_kind["case"])


# ============================================================
# UTILITIES
# ============================================================


def session():
    if not hasattr(local, "session"):
        local.session = requests.Session()
        local.session.headers.update({
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/pdf;q=0.9,*/*;q=0.5",
        })
    return local.session


def clean(v):
    return re.sub(r"\s+", " ", str(v or "")).strip()


def is_official_url(url):
    try:
        p = urlparse(url)
        return (
            p.scheme in ("http", "https")
            and (p.hostname or "").lower() in OFFICIAL_HOSTS
            and not p.username and not p.password
        )
    except (TypeError, ValueError):
        return False


def safe_url(url, base=""):
    try:
        c = urljoin(base, str(url or "").strip())
    except (TypeError, ValueError):
        return ""
    return c if is_official_url(c) else ""


def citation_from(text):
    for p in [
        r"\[\d{4}\]\s*KESC\s*\d+", r"\[\d{4}\]\s*KECA\s*\d+",
        r"\[\d{4}\]\s*KEHC\s*\d+", r"\[\d{4}\]\s*KEELC\s*\d+",
        r"\[\d{4}\]\s*KEELRC\s*\d+", r"\[\d{4}\]\s*KECR\s*\d+",
        r"\[\d{4}\]\s*KLR\s*\d+", r"\[\d{4}\]\s*KE[A-Z]+\s*\d+",
    ]:
        m = re.search(p, text or "", re.I)
        if m:
            return clean(m.group(0))
    return ""


def get_year(text):
    m = re.search(r"\b(19|20)\d{2}\b", text or "")
    return m.group(0) if m else ""


def _html_to_structured_text(node) -> str:
    for br in node.find_all("br"):
        br.replace_with("\n")
    for tag in node.find_all(
        ["p", "div", "h1", "h2", "h3", "h4", "h5", "h6", "li", "tr",
         "blockquote", "section", "article", "pre", "table"]
    ):
        try:
            tag.insert_before("\n\n")
            tag.append("\n\n")
        except Exception:
            pass
    raw = node.get_text()
    raw = re.sub(r"[ \t]+", " ", raw)
    raw = re.sub(r" ?\n ?", "\n", raw)
    raw = re.sub(r"\n{3,}", "\n\n", raw)
    return raw.strip()


def extract_pdf_text(pdf_bytes: bytes) -> str:
    if not _HAS_FITZ:
        return ""
    try:
        doc = fitz.open(stream=pdf_bytes, filetype="pdf")
        parts = [page.get_text() for page in doc]
        doc.close()
        text = "\n".join(parts)
        text = re.sub(r"[ \t]+", " ", text)
        text = re.sub(r"\n{3,}", "\n\n", text)
        return text.strip()
    except Exception as exc:
        log.warning("PDF extract failed: %s", exc)
        return ""


# ============================================================
# ACT CONTENT EXTRACTION
# ============================================================

_NOISE_SELECTORS = (
    "nav", "header", "footer", "aside", "button",
    "[role='button']", "[role='navigation']",
    "script", "style", "noscript", "svg", "iframe",
    ".share", "[class*='share-']", "[class*='shareButton']",
    ".social", "[class*='social']",
    ".related-documents", ".related", "[class*='related-doc']",
    ".sidebar", "[class*='sidebar']", "[class*='sideNav']",
    ".breadcrumb", "[class*='breadcrumb']",
    ".toolbar", "[class*='toolbar']",
    ".document-detail", ".document-metadata", "[class*='documentDetail']",
    ".actions", "[class*='actions']",
    ".toc", "[class*='tocSidebar']",
    ".citation-copy", "[class*='citationCopy']",
    ".download", "[class*='downloadButton']",
    ".modal", "[class*='modal']", ".toast", "[class*='toast']",
    ".back-to-top", "[class*='backToTop']",
    "[class*='reportProblem']", "[class*='report-problem']",
    "[aria-label*='Share']", "[aria-label*='share']",
    "[aria-label*='Download']", "[aria-label*='download']",
)

_AKN_CONTENT_SELECTORS = (
    ".akn-akoma-ntoso", ".akn-act", ".akn-judgment", ".akn-body", ".akn-doc",
    "[data-akn-content]",
)

_NOISE_TEXT_RE = re.compile(
    r"^(?:Share(?: this document)?(?: on .+)?(?: opens in new tab)?"
    r"|Report a problem|Download(?: PDF| original enactment)?(?:\s*\([^)]*\))?"
    r"|Copy citation|Copy|Share|Document detail|Related documents|Citations?"
    r"|\d+\s*/\s*\d+|Language|Date|Original enactment"
    r"|This feature is not currently available|To the top|▲|English)\s*$",
    re.I,
)


def _filter_noise_lines(body: str) -> str:
    kept = []
    for line in body.split("\n"):
        s = line.strip()
        if not s:
            kept.append("")
            continue
        if _NOISE_TEXT_RE.match(s):
            continue
        kept.append(line)
    return re.sub(r"\n{3,}", "\n\n", "\n".join(kept)).strip()


def _strip_chrome(soup):
    for sel in _NOISE_SELECTORS:
        try:
            for el in soup.select(sel):
                el.decompose()
        except Exception:
            pass


def _extract_from_akn_html(html: str) -> str:
    soup = BeautifulSoup(html, "html.parser")
    _strip_chrome(soup)
    best = ""
    for sel in _AKN_CONTENT_SELECTORS:
        try:
            for node in soup.select(sel):
                text = _filter_noise_lines(_html_to_structured_text(node))
                if len(text) > len(best):
                    best = text
        except Exception:
            pass
        if len(best) > 3000:
            break
    if not best:
        for sel in ("article", "main"):
            try:
                node = soup.select_one(sel)
                if node:
                    text = _filter_noise_lines(_html_to_structured_text(node))
                    if len(text) > len(best):
                        best = text
            except Exception:
                pass
    return best


def extract_from_akn(akn: dict | None) -> str:
    if not akn:
        return ""
    fmt, content = akn["format"], akn["content"]
    if fmt == "json" and isinstance(content, dict):
        html = content.get("content") or content.get("body") or ""
        return _extract_from_akn_html(html) if isinstance(html, str) else ""
    if fmt == "html" and isinstance(content, str):
        return _extract_from_akn_html(content)
    return ""


# ── Act header parsing ────────────────────────────────────

_ACT_HEADING_RE = re.compile(
    r"^(.+?)\s+(?:NO\.?\s*\d+\s+OF\s+\d{4}|CAP\.?\s*\d+[A-Z]?)$", re.I,
)
_META_LINE_RE = re.compile(
    r"^(Published\s+in(?:\s+the)?\s+Kenya\s+Gazette"
    r"|Assented\s+to|Commenced|In\s+force)"
    r"(?:\s+on)?\s+(.+)$",
    re.I,
)


def _find_act_start(lines: list[str]) -> int:
    """Locate the first line of real act content, skipping cover + TOC pages."""
    # Find "AN ACT of Parliament" — reliable preamble anchor
    preamble_idx = None
    for i, line in enumerate(lines[:600]):
        if re.match(r"^An?\s+ACT\s+of\s+Parliament\b", line.strip(), re.I):
            preamble_idx = i
            break

    if preamble_idx is not None:
        for j in range(preamble_idx - 1, max(preamble_idx - 25, -1), -1):
            line = lines[j].strip()
            if not line:
                continue
            if _ACT_HEADING_RE.match(line) and line == line.upper():
                return j
            if (re.match(r"^[A-Z][A-Z\s,.\-&']+(?:ACT|CODE|BILL)\b", line)
                    and len(line) < 150):
                return j
        return preamble_idx

    # No preamble — look for Part or first numbered section
    for i, line in enumerate(lines[:600]):
        s = line.strip()
        if re.match(r"^Part\s+[IVXLCDM]+\s*[-–—:]", s, re.I):
            return i
        if re.match(r"^1\.\s+(?:Short\s+title|Citation|Preliminary|Interpretation)\b",
                    s, re.I):
            return i
    return 0


def parse_act_header(content: str) -> dict:
    """
    Split raw act text into:
      title, act_number, metadata[], preamble, remaining_lines
    Skips anything before the act heading (cover, TOC, licence pages).
    """
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

        # "GAMBLING CONTROL ACT NO.14 OF 2025"
        m = _ACT_HEADING_RE.match(stripped)
        if m and stripped == stripped.upper() and len(stripped) < 250:
            title = clean(m.group(1))
            act_number = clean(m.group(2))
            i += 1
            continue

        # Standalone all-caps title
        if (not title and stripped == stripped.upper() and len(stripped) < 200
                and any(w in stripped for w in ("ACT", "CODE", "CONSTITUTION", "BILL"))):
            title = stripped
            i += 1
            continue

        # Standalone number line
        if (not act_number
                and re.match(r"^(?:NO\.?\s*\d+\s+OF\s+\d{4}|CAP\.?\s*\d+[A-Z]?)$",
                             stripped, re.I)):
            act_number = stripped
            i += 1
            continue

        # Metadata
        mm = _META_LINE_RE.match(stripped)
        if mm:
            label = clean(mm.group(1))
            value = clean(mm.group(2)).strip(" :")
            metadata.append({"label": label, "value": value})
            i += 1
            continue

        # Preamble "AN ACT of Parliament..."
        if re.match(r"^An?\s+ACT\s+of\s+Parliament\b", stripped, re.I):
            preamble_parts = [stripped]
            j = i + 1
            while j < len(lines):
                nxt = lines[j].strip()
                if not nxt:
                    j += 1
                    continue
                if re.match(r"^(?:Part\s+[IVXLCDM]|\d{1,3}[A-Z]?\.\s+[A-Z])",
                            nxt, re.I):
                    break
                preamble_parts.append(nxt)
                j += 1
            preamble = clean(" ".join(preamble_parts))
            body_start = j
            break

        # First Part or numbered section — no preamble
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


# ============================================================
# CASE HEADER
# ============================================================

_CORAM_RE = re.compile(r"^\(?\s*CORAM", re.I)
_CASE_NUM_RE = re.compile(
    r"\b(?:"
    r"CIVIL|CRIMINAL|MISC(?:ELLANEOUS)?|CONSTITUTIONAL|ELECTION|PETITION|"
    r"APPEAL|SUIT|CAUSE|COMMERCIAL|JUDICIAL\s+REVIEW|"
    r"HCC|HCCC|HCCRC|HCCR|CMCC|CMCR|ELC|ELRC|KESC|KECA|KEHC|JR|"
    r"TRIBUNAL|REFERENCE"
    r")[A-Z\.\s]*NO\.?\s*\d+\s+OF\s+\d{4}",
    re.I,
)
_JUDGE_RE = re.compile(
    r"^[A-Z][A-Za-z\.\s\-&',]{2,50}(?:,\s*(?:J|JA|JJA|JSC|CJ|DCJ|P|"
    r"J\.|JA\.|JJA\.|JSC\.|P\.)\.?)(?:\s*\(.*\))?\s*$",
)
_DATE_RE = re.compile(
    r"^(\d{1,2}(?:st|nd|rd|th)?\s+(?:day\s+of\s+)?[A-Z]+\s*,?\s*\d{4}"
    r"|[A-Z]+\s+\d{1,2}(?:st|nd|rd|th)?\s*,?\s*\d{4}"
    r"|\d{1,2}[/.-]\d{1,2}[/.-]\d{2,4})\s*$",
    re.I,
)
_DOC_TYPE_HEAD_RE = re.compile(
    r"^(?:RULING|JUDGMENT|DECISION|ORDER|AWARD|SENTENCE|"
    r"RULING\s+AND\s+(?:ORDER|DECREE)|"
    r"JUDGMENT\s+AND\s+(?:DECREE|ORDER)|"
    r"ORDER\s+AND\s+DECREE|"
    r"JUDGMENT\s+OF\s+THE\s+COURT|"
    r"RULING\s+OF\s+THE\s+COURT|"
    r"DECISION\s+OF\s+THE\s+COURT|"
    r"JUDGMENT\s+OF\s+THE\s+TRIBUNAL)$",
    re.I,
)
_ROLE_RE = re.compile(
    r"\b(?:\d{1,2}(?:ST|ND|RD|TH)\s+)?"
    r"(?:APPELLANT|RESPONDENT|PLAINTIFF|DEFENDANT|PETITIONER|"
    r"INTERESTED\s+PARTY|INTENDED\s+APPELLANT|INTENDED\s+RESPONDENT|"
    r"APPLICANT|OBJECTOR)\s*\.?\s*$",
    re.I,
)


def _combine_party_lines(lines: list[str]) -> list[str]:
    if not lines:
        return []
    result, current = [], []
    for line in lines:
        line = line.strip()
        if not line:
            continue
        current.append(line)
        if _ROLE_RE.search(line):
            result.append(" ".join(current))
            current = []
    if current:
        result.append(" ".join(current))
    return result


def extract_case_header(body: str) -> dict:
    lines = [l.strip() for l in (body or "").split("\n")]
    start = None
    for i, line in enumerate(lines):
        if not line:
            continue
        if re.search(r"\bREPUBLIC\s+OF\s+KENYA\b", line, re.I):
            start = i
            break
        if re.match(r"^IN\s+THE\s+", line, re.I) and (
            "COURT" in line.upper() or "TRIBUNAL" in line.upper()
            or "COMMISSION" in line.upper()
        ):
            start = i
            break
    if start is None:
        return {"body_start": 0}

    end = None
    doc_type = ""
    for i in range(start, min(start + 80, len(lines))):
        line = lines[i].strip()
        if not line or re.match(r"^[*\-\s]+$", line):
            continue
        m = _DOC_TYPE_HEAD_RE.match(line)
        if m:
            doc_type = m.group(0).upper()
            end = i + 1
            for j in range(i + 1, min(i + 5, len(lines))):
                nxt = lines[j].strip()
                if not nxt or re.match(r"^[*\-\s]+$", nxt):
                    end = j + 1
                    continue
                if _DOC_TYPE_HEAD_RE.match(nxt):
                    end = j + 1
                    continue
                break
            break
        if re.match(r"^\[\d{1,4}\]\s", line) or re.match(r"^\d{1,3}\.\s+[A-Z]", line):
            end = i
            break
    if end is None:
        end = start + 40 if len(lines) > start + 40 else len(lines)

    header_lines = lines[start:end]
    republic = ""
    court_lines: list[str] = []
    coram = ""
    case_number = ""
    judges: list[str] = []
    dates: list[str] = []
    parties_before: list[str] = []
    parties_after: list[str] = []
    parenthetical_lines: list[str] = []
    state = 0
    divider_text = ""
    doc_type_final = doc_type
    in_paren = False

    for raw in header_lines:
        line = raw.strip()
        if not line or re.match(r"^[*\-\s]+$", line):
            continue
        if in_paren:
            parenthetical_lines.append(line)
            if line.rstrip().endswith(")"):
                in_paren = False
            continue
        if re.search(r"\bREPUBLIC\s+OF\s+KENYA\b", line, re.I):
            republic = "REPUBLIC OF KENYA"
            continue
        if _CORAM_RE.match(line):
            coram = line
            continue
        if _CASE_NUM_RE.search(line):
            case_number = line
            continue
        if re.match(r"^IN\s+THE\s+", line, re.I):
            court_lines.append(line)
            continue
        if re.match(r"^AT\s+[A-Z][A-Z\s]+$", line, re.I) and len(line) < 40:
            court_lines.append(line)
            continue
        dm = _DOC_TYPE_HEAD_RE.match(line)
        if dm:
            doc_type_final = dm.group(0).upper()
            continue
        upper = line.upper().strip()
        if upper == "BETWEEN":
            state = 1
            divider_text = divider_text or "BETWEEN"
            continue
        if upper in ("VERSUS", "VS", "VS.", "—VERSUS—", "-VS-"):
            state = 2
            divider_text = divider_text or "VERSUS"
            continue
        if upper == "AND" and len(line) < 8 and parties_before:
            state = 2
            divider_text = divider_text or "AND"
            continue
        if line.startswith("("):
            parenthetical_lines.append(line)
            if not line.rstrip().endswith(")"):
                in_paren = True
            continue
        if _JUDGE_RE.match(line):
            judges.append(line)
            continue
        if _DATE_RE.match(line):
            dates.append(line)
            continue
        if state == 2:
            parties_after.append(line)
        else:
            parties_before.append(line)

    return {
        "republic": republic,
        "court_lines": court_lines,
        "coram": coram,
        "case_number": case_number,
        "judges": judges,
        "dates": dates,
        "divider": divider_text,
        "parties_before": _combine_party_lines(parties_before),
        "parties_after": _combine_party_lines(parties_after),
        "parenthetical": " ".join(parenthetical_lines),
        "doc_type": doc_type_final,
        "body_start": end,
    }


# ============================================================
# MARKERS / CONSTITUTION
# ============================================================

_CONSTITUTION_CACHE: list | None = None
_CONSTITUTION_LOCK = threading.Lock()

_ROMAN = {"i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x",
          "xi", "xii", "xiii", "xiv", "xv", "xvi", "xvii", "xviii", "xix", "xx"}

_ANY_MARKER_RE = re.compile(
    r"(\((?:\d{1,3}|[a-z]{1,3}|[ivxlc]+)\)|(?:\d{1,3}|[a-z]{1,3}|[ivxlc]+)[.)])"
    r"(?=\s)", re.I,
)


def _is_marker_start(text: str, pos: int) -> bool:
    if pos == 0:
        return True
    before = text[:pos]
    if before.endswith("\n"):
        return True
    stripped = before.rstrip()
    if not stripped:
        return True
    if stripped[-1] in ".;:,—–-":
        return True
    if stripped.lower().endswith((" and", " or")):
        return True
    return False


def split_marked_items(text: str) -> list[tuple[str, str]]:
    if not text:
        return []
    matches = [m for m in _ANY_MARKER_RE.finditer(text) if _is_marker_start(text, m.start())]
    if not matches:
        return [("", text.strip())]
    result: list[tuple[str, str]] = []
    if matches[0].start() > 0:
        prefix = text[: matches[0].start()].strip()
        if prefix:
            result.append(("", prefix))
    for i, m in enumerate(matches):
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[start:end].strip()
        if body:
            result.append((m.group(1), body))
    return result or [("", text.strip())]


def load_constitution_articles() -> list:
    global _CONSTITUTION_CACHE
    if _CONSTITUTION_CACHE is not None:
        return _CONSTITUTION_CACHE
    with _CONSTITUTION_LOCK:
        if _CONSTITUTION_CACHE is not None:
            return _CONSTITUTION_CACHE
        try:
            with open(CONSTITUTION_JSON_PATH, encoding="utf-8") as f:
                _CONSTITUTION_CACHE = json.load(f)
        except Exception:
            _CONSTITUTION_CACHE = []
    return _CONSTITUTION_CACHE


def build_constitution_toc() -> list:
    articles = load_constitution_articles()
    chapters: dict[int, dict] = {}
    for art in articles:
        chapter = art.get("chapter")
        if not chapter or len(chapter) < 2:
            continue
        ch_num, ch_title = chapter[0], chapter[1]
        chapters.setdefault(ch_num, {
            "number": ch_num, "title": ch_title, "parts": {}, "articles": [],
        })
        ch = chapters[ch_num]
        part = art.get("part")
        if part and len(part) >= 2:
            p_num, p_title = part[0], part[1]
            ch["parts"].setdefault(p_num, {"number": p_num, "title": p_title, "articles": []})
            ch["parts"][p_num]["articles"].append({"number": art["number"], "title": art["title"]})
        else:
            ch["articles"].append({"number": art["number"], "title": art["title"]})
    return [
        {**chapters[n], "parts": [chapters[n]["parts"][k] for k in sorted(chapters[n]["parts"].keys())]}
        for n in sorted(chapters.keys())
    ]


def parse_constitution_paragraphs(lines: list[str]) -> list[dict]:
    marker_at_start = re.compile(r"^\((\d{1,3}|[a-zA-Z]{1,3}|[ivxlc]+)\)\s*", re.I)
    merged: list[str] = []
    for raw in lines or []:
        line = (raw or "").strip()
        if not line:
            continue
        if marker_at_start.match(line) or not merged:
            merged.append(line)
        else:
            merged[-1] = merged[-1] + " " + line

    entries: list[dict] = []
    for line in merged:
        m = re.match(r"^(\((?:\d{1,3}|[a-zA-Z]{1,3}|[ivxlc]+)\))\s*(.*)$", line, re.S)
        if m:
            entries.append({"marker": m.group(1), "text": m.group(2).strip()})
        else:
            entries.append({"marker": "", "text": line})

    for i, e in enumerate(entries):
        inner = e["marker"].strip("()").lower()
        if not inner or inner.isdigit():
            e["level"] = 0
        elif inner == "i":
            is_roman = False
            for j in range(i + 1, min(i + 6, len(entries))):
                nxt = entries[j]["marker"].strip("()").lower()
                if not nxt:
                    continue
                if nxt in _ROMAN and nxt != "i":
                    is_roman = True
                break
            e["level"] = 2 if is_roman else 1
        elif inner in _ROMAN:
            e["level"] = 2
        else:
            e["level"] = 1

    final: list[dict] = []
    for e in entries:
        items = split_marked_items(e["text"]) if e["marker"] else []
        if len([mk for mk, _ in items if mk]) >= 1 and len(items) > 1:
            for mk, body in items:
                if not body:
                    continue
                if not mk:
                    final.append({"marker": e["marker"], "text": body, "level": e["level"]})
                else:
                    inner = mk.strip("()").lower()
                    if inner.isdigit():
                        lvl = 0
                    elif inner in _ROMAN and inner != "i":
                        lvl = 2
                    elif inner == "i":
                        lvl = 2
                    else:
                        lvl = 1
                    final.append({"marker": mk, "text": body, "level": lvl})
        else:
            final.append(e)
    return final


# ============================================================
# CASE / STATUTE VIEWS
# ============================================================


def _split_case_paragraphs(body: str) -> list[dict]:
    body = re.sub(r"[ \t]+", " ", body or "")
    body = re.sub(r"\n{3,}", "\n\n", body)
    blocks = re.split(r"\n{2,}", body)
    out: list[dict] = []

    def _push(main_num: int, text: str, primary_type: str = "para"):
        items = split_marked_items(text)
        has_markers = any(mk for mk, _ in items)
        if has_markers and len(items) > 1:
            for mk, sub in items:
                if not sub:
                    continue
                if not mk:
                    out.append({"number": main_num, "text": sub, "type": primary_type})
                else:
                    out.append({"number": 0, "marker": mk, "text": sub, "type": "subitem"})
        else:
            out.append({"number": main_num, "text": text, "type": primary_type})

    for block in blocks:
        block = block.strip()
        if not block or re.match(r"^[*\-\s_=•]+$", block):
            continue
        m = re.match(r"^\[(\d{1,4})\]\s*(.*)", block, re.S)
        if m:
            _push(int(m.group(1)), m.group(2).strip())
            continue
        m = re.match(r"^(\d{1,3})\.\s+(.*)", block, re.S)
        if m and int(m.group(1)) < 500:
            _push(int(m.group(1)), m.group(2).strip())
            continue
        if len(block) < 120 and block == block.upper() and len(block.split()) < 15:
            out.append({"number": 0, "text": block, "type": "subheading"})
            continue
        if re.match(r"^[\"\u201c\u2018]", block):
            out.append({"number": 0, "text": block, "type": "quote"})
            continue
        _push(0, block)
    return out


def build_case_view(doc: dict) -> dict:
    body = doc.get("body") or ""
    body = re.sub(r"[ \t]+", " ", body)
    body = re.sub(r"\n{3,}", "\n\n", body)
    header = extract_case_header(body)
    body_start = header.get("body_start", 0)
    lines = body.split("\n")
    body_text = "\n".join(lines[body_start:]).strip()

    body_blocks = re.split(r"\n{2,}", body_text)
    signing_text = ""
    for i, block in enumerate(body_blocks):
        stripped = block.strip()
        if re.match(r"^(?:Dated|DATED)\b", stripped) or re.match(
            r"^(?:DATED\s+AND\s+DELIVERED|DELIVERED|SIGNED|RULING\s+DELIVERED"
            r"|JUDGMENT\s+DELIVERED|JUDGMENT\s+DELIVERED\s+VIRTUALLY"
            r"|DATED,?\s+SIGNED\s+AND\s+DELIVERED)", stripped, re.I,
        ):
            signing_text = "\n\n".join(b.strip() for b in body_blocks[i:] if b.strip())
            body_blocks = body_blocks[:i]
            break

    paragraphs = _split_case_paragraphs("\n\n".join(body_blocks))
    return {
        "kind": "case",
        "url": doc.get("url", ""),
        "title": doc.get("title") or "Untitled judgment",
        "citation": doc.get("citation") or "",
        "court": doc.get("court") or "",
        "year": doc.get("year") or "",
        "date": doc.get("date") or "",
        "republic": header.get("republic", ""),
        "court_lines": header.get("court_lines", []),
        "coram": header.get("coram", ""),
        "case_number": header.get("case_number", ""),
        "judges": header.get("judges", []),
        "dates": header.get("dates", []),
        "divider": header.get("divider", ""),
        "parties_before": header.get("parties_before", []),
        "parties_after": header.get("parties_after", []),
        "parenthetical": header.get("parenthetical", ""),
        "doc_type": header.get("doc_type", ""),
        "paragraphs": paragraphs,
        "signing": signing_text,
    }


_PART_RE = re.compile(r"^(Part\s+[IVXLCDM]+[A-Z]?)\s*[—\-–:.]?\s*(.*)$", re.I)
_SECTION_RE = re.compile(r"^(\d{1,3}[A-Z]?)\.\s+(.+)$", re.S)


def _level_from_marker(marker: str) -> int:
    if not marker:
        return 0
    inner = marker.strip("().").lower()
    if inner.isdigit():
        return 1
    if inner in _ROMAN and inner != "i":
        return 3
    if inner == "i":
        return 3
    return 2


def _looks_like_toc_line(text: str) -> bool:
    if re.search(r"[A-Za-z]\s+\d{1,3}\s+\d{1,3}\.\s+[A-Z]", text):
        return True
    matches = list(re.finditer(r"\b\d{1,3}\.\s+[A-Z][a-z]", text))
    return len(matches) >= 2 and len(text) < 800


def _parse_body_items(body: str) -> list[dict]:
    """Parse a statute body (already header-stripped) into parts + sections."""
    body = re.sub(r"[ \t]+", " ", body or "")
    body = re.sub(r"\n{3,}", "\n\n", body)
    blocks = [b.strip() for b in re.split(r"\n{2,}", body) if b.strip()]

    merged: list[str] = []
    i = 0
    while i < len(blocks):
        block = blocks[i]
        if re.match(r"^\d{1,3}[A-Z]?\.\s*$", block) and i + 1 < len(blocks):
            nxt = blocks[i + 1]
            if (nxt and not re.match(r"^\d{1,3}[A-Z]?\.\s", nxt)
                    and not _looks_like_toc_line(nxt)):
                merged.append(f"{block} {nxt}")
                i += 2
                continue
        merged.append(block)
        i += 1

    items: list[dict] = []
    current_section: dict | None = None

    for block in merged:
        pm = _PART_RE.match(block)
        if pm and len(block) < 300:
            items.append({
                "type": "part",
                "number": clean(pm.group(1)).upper(),
                "title": clean(pm.group(2)),
            })
            current_section = None
            continue

        sm = _SECTION_RE.match(block)
        if sm:
            num_raw = sm.group(1)
            try:
                num = int(num_raw.rstrip("ABCDEFGHIJKLMNOPQRSTUVWXYZ"))
                suffix = num_raw[len(str(num)):]
            except ValueError:
                num, suffix = None, ""
            if num is not None and num < 1000:
                rest = sm.group(2).strip()
                if _looks_like_toc_line(rest) or len(rest) > 500:
                    items.append({"type": "text", "body": block})
                    continue
                parts = rest.split("\n", 1)
                sec_title = parts[0].strip().rstrip(".")
                if len(sec_title) > 250:
                    items.append({"type": "text", "body": block})
                    continue
                sec_body = parts[1].strip() if len(parts) > 1 else ""
                current_section = {
                    "type": "section",
                    "number": f"{num}{suffix}" if suffix else num,
                    "title": sec_title,
                    "subsections": [],
                }
                if sec_body:
                    for mk, sub_body in split_marked_items(sec_body):
                        current_section["subsections"].append({
                            "level": _level_from_marker(mk),
                            "marker": mk, "text": sub_body,
                        })
                items.append(current_section)
                continue

        if current_section is not None:
            for mk, sub_body in split_marked_items(block):
                current_section["subsections"].append({
                    "level": _level_from_marker(mk),
                    "marker": mk, "text": sub_body,
                })
        else:
            items.append({"type": "text", "body": block})

    return items


def build_statute_view(doc: dict) -> dict:
    raw = doc.get("body") or ""
    raw = re.sub(r"[ \t]+", " ", raw)

    header = parse_act_header(raw)
    body_text = "\n".join(header["remaining_lines"])
    items = _parse_body_items(body_text)
    has_structure = any(it.get("type") in ("part", "section") for it in items)

    title = header["title"] or doc.get("title") or ""
    act_number = header["act_number"] or doc.get("citation") or ""
    metadata = header["metadata"] or []
    preamble = header["preamble"] or ""

    raw_body = "" if has_structure else body_text
    if looks_like_chrome(raw_body):
        raw_body = ""

    # Aliases from DB
    aliases_list = []
    try:
        aliases_list = json.loads(doc.get("aliases") or "[]")
    except Exception:
        pass

    return {
        "kind": "statute",
        "url": doc.get("url", ""),
        "title": title or "Untitled statute",
        "citation": act_number,
        "aliases": aliases_list,
        "metadata": metadata,
        "preamble": preamble,
        "items": items,
        "raw_body": raw_body,
    }


# ============================================================
# JSON STORAGE
# ============================================================

_INVALID_FS_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')


def _sanitize_filename(name: str, max_len: int = 120) -> str:
    if not name:
        return "document"
    s = _INVALID_FS_CHARS.sub("_", name)
    s = re.sub(r"\s+", " ", s).strip().rstrip(". ")
    if len(s) > max_len:
        s = s[:max_len].rstrip()
    return s or "document"


def json_filename_for(doc: dict) -> Path:
    title = doc.get("title") or "Library document"
    citation = clean(doc.get("citation") or "")
    parts = [_sanitize_filename(title, max_len=100)]
    if citation:
        parts.append(_sanitize_filename(citation, max_len=50))
    base = " - ".join(p for p in parts if p).strip() or "document"
    target = JSON_DIR / f"{base}.json"
    if target.exists():
        url = doc.get("url") or ""
        if url:
            marker = target.with_suffix(".url")
            if marker.exists():
                try:
                    if marker.read_text(encoding="utf-8").strip() == url:
                        return target
                except Exception:
                    pass
            suffix = hashlib.sha1(url.encode("utf-8")).hexdigest()[:6]
            target = JSON_DIR / f"{base} [{suffix}].json"
    return target


def save_structured_json(url: str, kind: str, data: dict) -> Path | None:
    doc = get_document(url)
    if not doc:
        return None
    try:
        data = {**data, "v": SCHEMA_VERSIONS.get(kind, 1)}
        target = json_filename_for(doc)
        target.write_text(
            json.dumps(data, ensure_ascii=False, separators=(",", ":")),
            encoding="utf-8",
        )
        try:
            target.with_suffix(".url").write_text(url, encoding="utf-8")
        except Exception:
            pass
        with db() as con:
            con.execute(
                "UPDATE documents SET pdf_path=?, pdf_status='json' WHERE url=?",
                (str(target), url),
            )
        return target
    except Exception as exc:
        log.warning("JSON save failed for %s: %s", url, exc)
        return None


def load_structured_json(url: str, expected_kind: str) -> dict | None:
    doc = get_document(url)
    if not doc or doc.get("pdf_status") != "json":
        return None
    path = Path(doc.get("pdf_path") or "")
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("kind") != expected_kind:
            return None
        if data.get("v", 1) < SCHEMA_VERSIONS.get(expected_kind, 1):
            return None
        if expected_kind == "statute":
            raw = data.get("raw_body") or ""
            items = data.get("items") or []
            has_structure = any(it.get("type") in ("part", "section") for it in items)
            if looks_like_chrome(raw):
                return None
            if not has_structure and not looks_like_act_text(raw):
                return None
        return data
    except Exception:
        pass
    return None


# ============================================================
# DOCUMENT STORAGE
# ============================================================


def save_document(item) -> int | None:
    url = safe_url(item.get("url", ""))
    if not url:
        return None
    kind = determine_kind(url, item.get("kind"))
    body = item.get("body", "") or ""
    if kind == "statute" and body and looks_like_chrome(body):
        log.info("Rejecting chrome body for %s", url)
        body = ""
    pdf_status = "json" if body else item.get("pdf_status", "not_found")

    aliases = item.get("aliases") or []
    if isinstance(aliases, str):
        try:
            aliases = json.loads(aliases)
        except Exception:
            aliases = []
    if not isinstance(aliases, list):
        aliases = []
    aliases_json = json.dumps(aliases)

    with db() as con:
        old = con.execute("SELECT id, kind FROM documents WHERE url=?", (url,)).fetchone()
        old_kind = old["kind"] if old else None
        con.execute("""
            INSERT INTO documents(
                url,kind,title,citation,court,year,date,body,pdf_url,
                pdf_status,aliases,source,fetched_at,relevance
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            ON CONFLICT(url) DO UPDATE SET
                kind=excluded.kind,
                title=CASE WHEN excluded.title!='' THEN excluded.title ELSE documents.title END,
                citation=CASE WHEN excluded.citation!='' THEN excluded.citation ELSE documents.citation END,
                court=CASE WHEN excluded.court!='' THEN excluded.court ELSE documents.court END,
                year=CASE WHEN excluded.year!='' THEN excluded.year ELSE documents.year END,
                date=CASE WHEN excluded.date!='' THEN excluded.date ELSE documents.date END,
                body=CASE WHEN excluded.body!='' THEN excluded.body ELSE documents.body END,
                pdf_url=CASE WHEN excluded.pdf_url!='' THEN excluded.pdf_url ELSE documents.pdf_url END,
                pdf_status=CASE WHEN excluded.body!='' THEN 'json' ELSE documents.pdf_status END,
                aliases=CASE WHEN excluded.aliases!='[]' THEN excluded.aliases ELSE documents.aliases END,
                fetched_at=CASE WHEN excluded.body!='' THEN excluded.fetched_at ELSE documents.fetched_at END,
                relevance=MAX(documents.relevance, excluded.relevance)
        """, (
            url, kind, clean(item.get("title")), clean(item.get("citation")),
            clean(item.get("court")), clean(item.get("year")), clean(item.get("date")),
            body[:500_000], safe_url(item.get("pdf_url", ""), url),
            pdf_status, aliases_json,
            item.get("source", "Library"),
            time.time() if body else 0,
            float(item.get("relevance", 0) or 0),
        ))
        row = con.execute("SELECT id, kind FROM documents WHERE url=?", (url,)).fetchone()
        doc_id = row["id"] if row else None
        final_kind = row["kind"] if row else kind

    if doc_id:
        if old_kind and old_kind != final_kind:
            old_idx = _index_for_kind(old_kind)
            if old_idx:
                old_idx.remove_document(doc_id)
        idx = _index_for_kind(final_kind)
        if idx:
            idx.remove_document(doc_id)
            idx.index_document(
                doc_id, item.get("title", ""), item.get("citation", ""),
                body, url, item.get("court", ""), item.get("year", ""),
                aliases_list=aliases,
            )
    return doc_id


def get_document(url):
    with db() as con:
        row = con.execute("SELECT * FROM documents WHERE url=?", (url,)).fetchone()
    return dict(row) if row else None


# ============================================================
# FETCHERS
# ============================================================


def fetch_act(url: str, title: str, cap: str = "", year: str = "",
              aliases: list | None = None) -> bool:
    url = safe_url(url)
    if not url:
        return False

    existing = get_document(url)
    if existing and existing.get("body"):
        if (not looks_like_chrome(existing["body"])
                and looks_like_act_text(existing["body"])):
            return True

    akn = KL.fetch_akn(url)
    body = extract_from_akn(akn)

    if not body or not looks_like_act_text(body):
        pdf_text = KL.fetch_pdf_text(url)
        if pdf_text and looks_like_act_text(pdf_text) and len(pdf_text) > len(body):
            body = pdf_text

    if not body or not looks_like_act_text(body):
        log.info("Act %r: no valid content from %s", title, url)
        return False

    alias_list = list(aliases or [])
    if cap:
        for c in (cap, cap.replace(".", " ")):
            if c.lower() not in [a.lower() for a in alias_list]:
                alias_list.append(c)
    if year:
        for y in (f"Act No. {year}", f"{title}, {year}"):
            if y.lower() not in [a.lower() for a in alias_list]:
                alias_list.append(y)

    save_document({
        "url": url, "kind": "statute",
        "title": title or "Untitled Act",
        "citation": cap, "year": year,
        "aliases": alias_list,
        "body": body,
    })
    doc = get_document(url)
    if doc:
        save_structured_json(url, "statute", build_statute_view(doc))
    return True


def fetch_case(url: str, title: str = "", citation: str = "",
               court: str = "", year: str = "") -> bool:
    url = safe_url(url)
    if not url or not is_individual_case_url(url):
        return False
    existing = get_document(url)
    if existing and existing.get("body") and len(existing["body"]) > 500:
        return True

    akn = KL.fetch_akn(url)
    body = extract_from_akn(akn)

    if not body or len(body) < 1000:
        pdf_text = KL.fetch_pdf_text(url)
        if pdf_text and len(pdf_text) > len(body):
            body = pdf_text

    if not body or len(body) < 200:
        log.info("Case %r: no content from %s", title, url)
        return False

    if not citation:
        citation = citation_from(body[:5000])
    if not year:
        year = get_year(title or body[:2000])

    save_document({
        "url": url, "kind": "case",
        "title": title or "Untitled judgment",
        "citation": citation, "court": court, "year": year,
        "body": body,
    })
    doc = get_document(url)
    if doc:
        save_structured_json(url, "case", build_case_view(doc))
    return True


def fetch_document(url, kind_hint="case"):
    url = safe_url(url)
    if not url:
        return None
    kind = determine_kind(url, kind_hint)
    if kind == "case":
        fetch_case(url)
    elif kind == "statute":
        fetch_act(url, "")
    return get_document(url)


# ============================================================
# SEARCH HELPER — local + Kenya Law
# ============================================================


def search_kenyalaw(query: str, kind: str, limit: int = 10) -> list[dict]:
    if not query or not check_online():
        return []
    fetched = []
    if kind == "statute":
        for r in KL.search(query, kind="act", max_results=limit * 2)[:limit]:
            if fetch_act(r["url"], r["title"]):
                d = get_document(r["url"])
                if d:
                    fetched.append(d)
    elif kind == "case":
        for r in KL.search(query, kind="judgment", max_results=limit * 2)[:limit]:
            if fetch_case(r["url"], title=r["title"]):
                d = get_document(r["url"])
                if d:
                    fetched.append(d)
    return fetched


# ============================================================
# PUBLIC DOC
# ============================================================


def public_document(item):
    body = item.get("body", "") or ""
    aliases = []
    try:
        aliases = json.loads(item.get("aliases") or "[]")
    except Exception:
        pass
    return {
        "id": item.get("id"),
        "url": item.get("url", ""),
        "kind": item.get("kind", "case"),
        "type": item.get("kind", "case"),
        "title": item.get("title") or "Untitled",
        "citation": item.get("citation", ""),
        "court": item.get("court", ""),
        "year": item.get("year", ""),
        "date": item.get("date", ""),
        "aliases": aliases,
        "excerpt": clean(body)[:650],
        "has_body": bool(body.strip()),
        "source": item.get("source", "Library"),
    }


# ============================================================
# BOOTSTRAP
# ============================================================


def set_bootstrap_state(**kw):
    with bootstrap_state_lock:
        bootstrap_state.update(kw)


def bootstrap_acts_from_list():
    acts = load_acts_manifest()
    if not acts:
        log.warning("No acts manifest")
        return
    if not check_online():
        log.warning("Offline — skipping acts bootstrap")
        return

    with db() as con:
        cached = con.execute(
            "SELECT title, body FROM documents WHERE kind='statute' AND body != ''"
        ).fetchall()
    cached_titles = set()
    for r in cached:
        body = r["body"] or ""
        if looks_like_chrome(body) or not looks_like_act_text(body):
            continue
        cached_titles.add(KL.norm_title(r["title"]))

    pending = [a for a in acts
               if KL.norm_title(a.get("title") or "") not in cached_titles
               and "constitution of kenya" not in (a.get("title") or "").lower()]

    log.info("Acts bootstrap: %d/%d cached, %d to fetch",
             len(acts) - len(pending), len(acts), len(pending))

    set_bootstrap_state(
        running=True, started_at=time.time(), finished_at=0.0, kind="acts",
        total=len(acts), completed=len(acts) - len(pending), failed=0,
        detail="Building legislation index…",
    )

    try:
        index = KL.crawl_legislation()
        title_to_url = {KL.norm_title(it["title"]): it["url"] for it in index}
        log.info("Legislation index: %d entries", len(index))
    except Exception:
        log.exception("legislation index failed")
        title_to_url = {}

    completed = len(acts) - len(pending)
    failed = 0
    try:
        for act in pending:
            title = (act.get("title") or "").strip()
            cap = act.get("cap") or ""
            year = act.get("year")
            aliases = act.get("aliases") or []
            if not title:
                continue

            set_bootstrap_state(detail=f"Fetching: {title}")
            url = title_to_url.get(KL.norm_title(title))
            if not url:
                try:
                    hits = KL.search(title, kind="act", max_results=3)
                    if hits:
                        url = hits[0]["url"]
                except Exception:
                    pass
            if not url:
                failed += 1
                set_bootstrap_state(failed=failed)
                continue

            try:
                ok = fetch_act(url, title, cap, str(year) if year else "", aliases)
                if ok:
                    completed += 1
                    set_bootstrap_state(completed=completed)
                else:
                    failed += 1
                    set_bootstrap_state(failed=failed)
            except Exception as exc:
                log.info("Act %s fetch failed: %s", title, exc)
                failed += 1
                set_bootstrap_state(failed=failed)
            time.sleep(0.15)
        log.info("Acts done: %d ok, %d failed", completed, failed)
    except Exception:
        log.exception("Acts bootstrap crashed")
    finally:
        set_bootstrap_state(
            running=False, finished_at=time.time(),
            detail=f"{completed} acts ready ({failed} unavailable)",
        )


def bootstrap_cases():
    if not check_online():
        return
    set_bootstrap_state(
        running=True, started_at=time.time(), finished_at=0.0, kind="cases",
        total=0, completed=0, failed=0, detail="Fetching cases from Kenya Law",
    )
    try:
        items = KL.crawl_judgments(max_pages=10)
        log.info("Judgments index: %d entries", len(items))
        set_bootstrap_state(total=len(items), detail="Fetching cases")
        for i, it in enumerate(items[:60]):
            try:
                fetch_case(it["url"], title=it["title"])
                set_bootstrap_state(completed=i + 1)
            except Exception:
                pass
            time.sleep(0.15)
    except Exception:
        log.exception("cases bootstrap failed")
    finally:
        with bootstrap_state_lock:
            done = bootstrap_state.get("completed", 0)
        set_bootstrap_state(
            running=False, finished_at=time.time(),
            detail=f"{done} cases ready",
        )


def bootstrap_library():
    try:
        bootstrap_acts_from_list()
    except Exception:
        log.exception("acts bootstrap failed")
    try:
        bootstrap_cases()
    except Exception:
        log.exception("cases bootstrap failed")


def start_bootstrap():
    global bootstrap_started
    with bootstrap_lock:
        if bootstrap_started:
            return
        bootstrap_started = True
    BACKGROUND_POOL.submit(bootstrap_library)


# ============================================================
# ROUTES
# ============================================================


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
            "SELECT COUNT(*) FROM documents WHERE kind='statute' AND body != ''"
        ).fetchone()[0]
        cases = con.execute(
            "SELECT COUNT(*) FROM documents WHERE kind='case' AND body != ''"
        ).fetchone()[0]
    return jsonify({
        "ok": True,
        "online": check_online(),
        "statute_docs": statutes,
        "case_docs": cases,
        "constitution_articles_loaded": len(load_constitution_articles()),
        "bootstrap_running": bootstrap_state["running"],
        "pymupdf": _HAS_FITZ,
    })


@app.get("/api/bootstrap/status")
def api_bootstrap_status():
    with bootstrap_state_lock:
        return jsonify(dict(bootstrap_state))


@app.get("/api/autocomplete")
def api_autocomplete():
    q = clean(request.args.get("q", ""))[:80]
    kind = request.args.get("kind", "all").lower()
    suggestions = []
    if kind == "all":
        for idx in _all_indexes():
            suggestions.extend(idx.autocomplete(q, limit=6))
    else:
        idx = _index_for_kind(kind)
        if idx:
            suggestions = idx.autocomplete(q, limit=12)
    seen, out = set(), []
    for s in suggestions:
        k = s.lower()
        if k and k not in seen:
            seen.add(k)
            out.append(s)
    return jsonify({"suggestions": out[:12]})


@app.post("/api/search")
def api_search():
    payload = request.get_json(silent=True) or {}
    query = clean(payload.get("query", ""))[:200]
    kind = payload.get("kind")
    if kind not in ("statute", "case", "constitution", "all"):
        kind = "all"
    if len(query) < 2:
        return jsonify({"error": "Enter at least two characters."}), 400

    local_results: list[dict] = []
    if kind == "all":
        for k, idx in (("constitution", CONSTITUTION_INDEX),
                       ("statute", STATUTE_INDEX), ("case", CASE_INDEX)):
            for h in idx.search(query, limit=MAX_RESULTS):
                local_results.append({**h, "kind": k})
    else:
        idx = _index_for_kind(kind)
        if idx:
            local_results = [{**h, "kind": kind} for h in idx.search(query, limit=MAX_RESULTS)]

    def hydrate(rows):
        urls = [r["url"] for r in rows if r.get("url")]
        if not urls:
            return []
        placeholders = ",".join("?" * len(urls))
        with db() as con:
            dbrows = con.execute(
                f"SELECT * FROM documents WHERE url IN ({placeholders})", urls
            ).fetchall()
        by_url = {r["url"]: dict(r) for r in dbrows}
        out = []
        for r in rows:
            full = by_url.get(r["url"])
            if full:
                full["score"] = r.get("score", 0)
                out.append(full)
        return out

    hydrated = hydrate(local_results)

    if kind == "statute":
        hydrated = [
            d for d in hydrated
            if is_act_url(d.get("url", "")) and d.get("body")
            and not looks_like_chrome(d["body"])
            and looks_like_act_text(d["body"])
        ]
    elif kind == "case":
        hydrated = [
            d for d in hydrated
            if is_individual_case_url(d.get("url", "")) and d.get("body")
        ]
    else:
        hydrated = [d for d in hydrated if d.get("body")]

    # Online fallback for cases AND statutes
    if kind in ("case", "statute") and len(hydrated) < 5 and check_online():
        try:
            live = search_kenyalaw(query, kind, limit=10)
            seen = {d["url"] for d in hydrated}
            for doc in live:
                if doc["url"] not in seen:
                    hydrated.append(doc)
                    seen.add(doc["url"])
        except Exception:
            log.exception("live search failed")

    if kind == "all":
        order = {"constitution": 0, "statute": 1, "case": 2}
        hydrated.sort(key=lambda d: (order.get(d.get("kind", "case"), 3),
                                     -float(d.get("score", 0) or 0)))

    return jsonify({
        "query": query,
        "kind": kind,
        "results": [public_document(d) for d in hydrated[:MAX_RESULTS]],
        "count": len(hydrated),
        "online_available": check_online() if not hydrated else True,
    })


@app.get("/api/library")
def library():
    kind = request.args.get("type", "case").lower()
    try:
        limit = max(1, min(int(request.args.get("limit", "500")), 500))
    except ValueError:
        limit = 500
    if kind not in ("constitution", "statute", "case", "all"):
        return jsonify({"error": "Unknown library category."}), 400

    if kind == "statute":
        where = "WHERE kind='statute' AND body != ''"
    elif kind == "constitution":
        where = "WHERE kind='constitution' AND body != ''"
    elif kind == "case":
        where = "WHERE kind='case' AND body != ''"
    else:
        where = "WHERE body != ''"

    sql = f"SELECT * FROM documents {where} ORDER BY title COLLATE NOCASE LIMIT ?"
    with db() as con:
        items = [dict(r) for r in con.execute(sql, (limit,)).fetchall()]

    if kind == "statute":
        items = [
            it for it in items
            if is_act_url(it.get("url", ""))
            and not looks_like_chrome(it.get("body", ""))
            and looks_like_act_text(it.get("body", ""))
        ]
    elif kind == "case":
        items = [it for it in items if is_individual_case_url(it.get("url", ""))]

    return jsonify({
        "documents": [public_document(x) for x in items],
        "kind": kind,
        "total": len(items),
        "online": check_online(),
        "bootstrap_running": bootstrap_state["running"],
        "bootstrap_kind": bootstrap_state.get("kind"),
        "bootstrap_completed": bootstrap_state.get("completed", 0),
        "bootstrap_total": bootstrap_state.get("total", 0),
    })


@app.get("/api/document/open")
def api_open_document_get():
    url = safe_url(request.args.get("url", "") or request.args.get("sourceUrl", ""))
    if not url:
        return jsonify({"error": "Invalid URL."}), 400
    doc = get_document(url)
    if not doc or not doc.get("body"):
        doc = fetch_document(url, doc.get("kind", "case") if doc else "case")
    if not doc:
        return jsonify({"error": "Could not retrieve document."}), 502
    return jsonify({"document": public_document(doc), "success": True})


# ============================================================
# CONSTITUTION / STRUCTURED VIEWS
# ============================================================


@app.get("/api/constitution/toc")
def api_constitution_toc():
    return jsonify({"chapters": build_constitution_toc()})


@app.get("/api/constitution/article/<int:number>")
def api_constitution_article(number: int):
    for art in load_constitution_articles():
        if art.get("number") == number:
            art = dict(art)
            art["paragraphs"] = parse_constitution_paragraphs(art.get("lines", []))
            return jsonify(art)
    return jsonify({"error": "Article not found"}), 404


@app.get("/api/constitution/search")
def api_constitution_search():
    q = clean(request.args.get("q", "")).lower()
    if not q:
        return jsonify({"results": []})
    results = []
    for art in load_constitution_articles():
        text = f"{art.get('title', '')} {' '.join(art.get('lines', []))}".lower()
        if q in text:
            results.append({
                "number": art["number"], "title": art["title"],
                "chapter": art.get("chapter"), "part": art.get("part"),
            })
        if len(results) >= 60:
            break
    return jsonify({"results": results})


@app.get("/api/case/structured")
def api_case_structured():
    url = safe_url(request.args.get("url", ""))
    if not url:
        return jsonify({"error": "Invalid URL"}), 400
    cached = load_structured_json(url, "case")
    if cached:
        return jsonify(cached)
    doc = get_document(url)
    if not doc or not doc.get("body"):
        fetch_case(url)
        doc = get_document(url)
    if not doc:
        return jsonify({"error": "Could not fetch document"}), 502
    data = build_case_view(doc)
    save_structured_json(url, "case", data)
    return jsonify(data)


@app.get("/api/statute/structured")
def api_statute_structured():
    url = safe_url(request.args.get("url", ""))
    if not url:
        return jsonify({"error": "Invalid URL"}), 400
    cached = load_structured_json(url, "statute")
    if cached:
        return jsonify(cached)
    doc = get_document(url)
    if not doc or not doc.get("body"):
        return jsonify({"error": "Not cached"}), 404
    if looks_like_chrome(doc["body"]):
        return jsonify({"error": "Chrome detected — will be refetched"}), 409
    data = build_statute_view(doc)
    save_structured_json(url, "statute", data)
    return jsonify(data)


# ============================================================
# MAINTENANCE
# ============================================================


@app.post("/api/maintenance/purge-chrome")
def api_purge_chrome():
    n = purge_chrome_statutes()
    rebuild_memory_indexes()
    return jsonify({"purged": n})


@app.post("/api/maintenance/refetch-acts")
def api_refetch_acts():
    if bootstrap_state["running"]:
        return jsonify({"error": "Bootstrap already running"}), 409
    BACKGROUND_POOL.submit(bootstrap_acts_from_list)
    return jsonify({"ok": True, "queued": True})


@app.post("/api/maintenance/refetch-cases")
def api_refetch_cases():
    if bootstrap_state["running"]:
        return jsonify({"error": "Bootstrap already running"}), 409
    BACKGROUND_POOL.submit(bootstrap_cases)
    return jsonify({"ok": True, "queued": True})


@app.post("/api/maintenance/rebuild-statute-json")
def api_rebuild_statute_json():
    rebuilt, failed = 0, 0
    with db() as con:
        rows = con.execute(
            "SELECT url FROM documents WHERE kind='statute' AND body != ''"
        ).fetchall()
    for r in rows:
        try:
            doc = get_document(r["url"])
            if doc and not looks_like_chrome(doc.get("body", "")):
                data = build_statute_view(doc)
                if save_structured_json(r["url"], "statute", data):
                    rebuilt += 1
                else:
                    failed += 1
            else:
                failed += 1
        except Exception:
            failed += 1
    return jsonify({"rebuilt": rebuilt, "failed": failed})


@app.errorhandler(HTTPException)
def http_error(error):
    if request.path.startswith("/api/"):
        return jsonify({"error": error.description}), error.code
    return error


@app.errorhandler(Exception)
def unexpected_error(error):
    log.exception("unexpected")
    if request.path.startswith("/api/"):
        return jsonify({"error": "Internal server error."}), 500
    return "Internal server error.", 500


# ============================================================
# BOOT
# ============================================================

init_db()
migrate_kinds()
purge_chrome_statutes()
rebuild_memory_indexes()
load_constitution_articles()
load_acts_manifest()
start_bootstrap()

if __name__ == "__main__":
    log.info("Library: http://%s:%s", HOST, PORT)
    app.run(host=HOST, port=PORT, debug=False, threaded=True, use_reloader=False)
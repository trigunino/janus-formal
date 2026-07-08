from __future__ import annotations

import csv
import re
import time
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urljoin
from urllib.request import Request, urlopen


MAP_URL = "https://januscosmologicalmodel.com/map"
RAW_DIR = Path("data/raw/janus_library")
DOC_PATH = Path("docs/janus_bibliography.md")
MANIFEST_PATH = RAW_DIR / "manifest.csv"
USER_AGENT = "janus-lab/0.1"


@dataclass
class Entry:
    ref_id: str
    title: str
    source_url: str
    origin: str
    year: str = ""
    pdf_url: str | None = None
    file_path: Path | None = None
    status: str = "pending"
    note: str = ""


class LinkParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[tuple[str, str]] = []
        self._href: str | None = None
        self._text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "a":
            attrs_dict = dict(attrs)
            self._href = attrs_dict.get("href")
            self._text = []

    def handle_data(self, data: str) -> None:
        if self._href is not None:
            self._text.append(data)

    def handle_endtag(self, tag: str) -> None:
        if tag == "a" and self._href is not None:
            text = " ".join("".join(self._text).split())
            self.links.append((text, self._href))
            self._href = None
            self._text = []


EXTRA_ENTRIES = [
    Entry(
        "X2022-hal-acceleration-cosmic-expansion",
        "Janus, the only cosmological model that explains the acceleration of cosmic expansion",
        "https://hal.science/hal-03834305v2",
        "hal precursor",
        "2022",
        pdf_url="https://hal.science/hal-03834305v2/document",
    ),
    Entry(
        "X2025-rebuttal-damour",
        "Rebuttal of Damour's criticism of the Janus model",
        "http://www.jp-petit.org/papers/cosmo/2025-06-19-Rebuttal%20of%20Damour%27s%20criticism%20of%20the%20Janus%20model.pdf",
        "jp-petit recent",
        "2025",
    ),
    Entry(
        "X2025-modele-janus-impasse",
        "Modele Janus Impasse",
        "http://www.jp-petit.org/papers/cosmo/2025-08-28-Modele-Janus-Impasse.pdf",
        "jp-petit recent",
        "2025",
    ),
    Entry(
        "X2025-kinetic-galactic",
        "Contribution of Kinetic Theory to Galactic Dynamics",
        "http://www.jp-petit.org/papers/cosmo/2025-10-14-Astroph-and-Space-Sci-Contribution-of-Kinetic-Theory-to-Galactic-Dynamics.pdf",
        "jp-petit recent",
        "2025",
    ),
    Entry(
        "X2025-plugstars-jmp",
        "Alternatives to Black Holes: Gravastars and Plugstars",
        "http://www.jp-petit.org/papers/cosmo/2025-10-14-JMP-Alternative-to-Black-Holes-Gravastars-and-Plugstars.pdf",
        "jp-petit recent",
        "2025",
    ),
    Entry(
        "X2026-black-hole-inconsistency-I",
        "Mathematical and Geometrical Inconsistency of the Black Hole Model. Part I",
        "http://www.jp-petit.org/papers/cosmo/2026-01-JMP-Mathematical-and-Geometrical-Inconsistency-of-the-Black-Hole-Model.Part%20I.pdf",
        "jp-petit recent",
        "2026",
    ),
    Entry(
        "X2026-black-hole-analytic-extension",
        "The black hole model goes with an analytic extension of spacetime",
        "http://www.jp-petit.org/papers/cosmo/2026-06-JMP-The%20black%20hole%20model%20goes%20with%20an%20analytic%20extension%20of%20spacetime.pdf",
        "jp-petit recent",
        "2026",
    ),
    Entry(
        "X2026-black-hole-inconsistency-II",
        "Mathematical and Geometrical Inconsistency of the Black Hole Model. Part II",
        "http://www.jp-petit.org/papers/cosmo/2026-Mathematical-and-Geometrical-Inconsistency-of-the-Black-Hole-Model.Part-II.pdf",
        "jp-petit recent",
        "2026",
    ),
    Entry(
        "X2026-expansion-desi",
        "Janus exact expansion solution and DESI",
        "http://www.jp-petit.org/papers/cosmo/2026-Expansion-exact-solution-2014-.pdf",
        "jp-petit recent",
        "2026",
    ),
    Entry(
        "X2026-variable-constants",
        "Alternative to Inflation: Variable Constants Regime",
        "http://www.jp-petit.org/papers/cosmo/2026-Alternative-to-Inflation-Variable-Constants-Regime.pdf",
        "jp-petit recent",
        "2026",
    ),
    Entry(
        "X2026-questionable-black-holes",
        "Questionable Black Holes",
        "http://www.jp-petit.org/papers/cosmo/2026-01-12-Journal-of-Modern-Physics-QUESTIONABLE-BLACK-HOLES.pdf",
        "jp-petit recent",
        "2026",
    ),
    Entry(
        "X2026-complex-reality",
        "The Real World as a part of a Complex Reality",
        "http://www.jp-petit.org/papers/cosmo/2026-07-07-Is%20the%20real%20world%20as%20a%20part%20of%20a%20complex%20reality.pdf",
        "jp-petit recent",
        "2026",
    ),
    Entry(
        "X2025-symplectic-hal",
        "Study of symmetries through the action on torsors of the Janus symplectic group",
        "http://www.jp-petit.org/papers/cosmo/2025-03-09-HAL-Studies-of-symmetries-through-the-action-on-torsors-of-the-Janus-sympkectic-group.pdf",
        "jp-petit recent",
        "2025",
    ),
    Entry(
        "X2025-bimetric-hal",
        "A bimetric cosmological model based on Andrei Sakharov's twin-universe approach",
        "http://www.jp-petit.org/papers/cosmo/2025-03-07-HAL-A-bimetric-model-based-on-Andrei-Sakharov's-twin-universe-approach.pdf",
        "jp-petit recent",
        "2025",
    ),
    Entry(
        "X2025-technical-book",
        "The Janus Cosmological Model",
        "http://www.jp-petit.org/papers/cosmo/2025-04-25-The-Janus-Cosmological-Model.pdf",
        "jp-petit recent book",
        "2025",
    ),
]

MAP_YEARS = {
    "M01": "1977",
    "M02": "1977",
    "M03": "1988",
    "M04": "1988",
    "M05": "1989",
    "M06": "1994",
    "M07": "1995",
    "M08": "2007",
    "M09": "2008",
    "M10": "2001",
    "M11": "2005",
    "M12": "2007",
    "M13": "2014",
    "M14": "2014",
    "M15": "2015",
    "M16": "2015",
    "M17": "2018",
    "M18": "2018",
    "M19": "2018",
    "M20": "2018",
    "M21": "2018",
    "M22": "2019",
    "M23": "2019",
    "M24": "2020",
    "M25": "2021",
    "M26": "2022",
    "M27": "2022",
    "M28": "2023",
    "M29": "2024",
    "M30": "2024",
    "M31": "2024",
}

PDF_OVERRIDES = {
    "M09": "http://www.jp-petit.org/papers/cosmo/2008-PIRT11.pdf",
    "M14": "http://www.jp-petit.org/papers/cosmo/2014-ModPhysLettA.pdf",
    "M21": "https://arxiv.org/pdf/1809.05046",
    "M24": "https://data.over-blog-kiwi.com/0/93/52/74/20241225/ob_9a1b78_2019-guay-qft.pdf",
    "M31": "http://www.jp-petit.org/papers/cosmo/2025-03-09-HAL-Studies-of-symmetries-through-the-action-on-torsors-of-the-Janus-sympkectic-group.pdf",
}


def fetch_text(url: str) -> str:
    request = Request(url, headers={"User-Agent": USER_AGENT})
    with urlopen(request, timeout=120) as response:
        return response.read().decode("utf-8", "replace")


def parse_map_entries() -> list[Entry]:
    html = fetch_text(MAP_URL)
    parser = LinkParser()
    parser.feed(html)

    entries: list[Entry] = []
    current_id: str | None = None
    for text, href in parser.links:
        href_abs = urljoin(MAP_URL, href)
        if text.isdigit():
            current_id = text
            continue
        if current_id is None:
            continue
        if not text or href_abs.startswith(f"{MAP_URL}#"):
            continue

        ref_id = f"M{int(current_id):02d}"
        title = text.strip().strip('"').strip(".")
        entries.append(
            Entry(
                ref_id=ref_id,
                title=title,
                source_url=href_abs,
                origin="januscosmologicalmodel.com/map",
                year=MAP_YEARS.get(ref_id, guess_year(title, href_abs)),
            )
        )
        current_id = None

    return entries


def guess_year(title: str, url: str) -> str:
    match = re.search(r"(19|20)\d{2}", f"{title} {url}")
    return match.group(0) if match else ""


def slugify(text: str, limit: int = 80) -> str:
    text = text.lower()
    text = re.sub(r"[^a-z0-9]+", "-", text)
    text = text.strip("-")
    return text[:limit].strip("-") or "paper"


def resolve_pdf_url(entry: Entry) -> str | None:
    if entry.ref_id in PDF_OVERRIDES:
        return PDF_OVERRIDES[entry.ref_id]

    if entry.pdf_url:
        return entry.pdf_url

    url = entry.source_url
    lower = url.lower()
    if lower.endswith(".pdf") or "/pdf/" in lower:
        return url

    arxiv_match = re.search(r"arxiv\.org/abs/([^?#]+)", url)
    if arxiv_match:
        return f"https://arxiv.org/pdf/{arxiv_match.group(1)}"

    if "iopscience.iop.org" in lower and lower.endswith("/pdf"):
        return url

    if "doi.org/10.1140/epjc" in lower:
        doi = url.split("doi.org/", 1)[1]
        return f"https://link.springer.com/content/pdf/{doi}.pdf"

    if "doi.org/10.1142/" in lower:
        doi = url.split("doi.org/", 1)[1]
        return f"https://www.worldscientific.com/doi/pdf/{doi}"

    return None


def safe_url(url: str) -> str:
    if " " not in url and "'" not in url:
        return url
    scheme, rest = url.split("://", 1)
    host, _, path = rest.partition("/")
    return f"{scheme}://{host}/{quote(path, safe='/:%')}"


def download_pdf(entry: Entry, force: bool = False) -> Entry:
    pdf_url = resolve_pdf_url(entry)
    entry.pdf_url = pdf_url
    if pdf_url is None:
        entry.status = "no_pdf_url"
        entry.note = "No direct PDF resolver implemented."
        return entry

    RAW_DIR.mkdir(parents=True, exist_ok=True)
    filename = f"{entry.ref_id}_{slugify(entry.title)}.pdf"
    destination = RAW_DIR / filename
    entry.file_path = destination

    if destination.exists() and destination.stat().st_size > 0 and not force:
        entry.status = "exists"
        return entry

    try:
        request = Request(safe_url(pdf_url), headers={"User-Agent": USER_AGENT})
        with urlopen(request, timeout=180) as response:
            data = response.read()
    except (HTTPError, URLError, TimeoutError) as exc:
        entry.status = "failed"
        entry.note = str(exc)
        return entry

    if not data.startswith(b"%PDF"):
        entry.status = "not_pdf"
        entry.note = f"Downloaded {len(data)} bytes but content is not a PDF."
        return entry

    destination.write_bytes(data)
    entry.status = "downloaded"
    entry.note = f"{len(data)} bytes"
    return entry


def dedupe_entries(entries: list[Entry]) -> list[Entry]:
    seen: set[str] = set()
    result: list[Entry] = []
    for entry in entries:
        key = entry.source_url.lower()
        if key in seen:
            continue
        seen.add(key)
        result.append(entry)
    return result


def write_manifest(entries: list[Entry]) -> None:
    RAW_DIR.mkdir(parents=True, exist_ok=True)
    with MANIFEST_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "ref_id",
                "year",
                "title",
                "origin",
                "source_url",
                "pdf_url",
                "file_path",
                "status",
                "note",
            ],
        )
        writer.writeheader()
        for entry in entries:
            writer.writerow(
                {
                    "ref_id": entry.ref_id,
                    "year": entry.year,
                    "title": entry.title,
                    "origin": entry.origin,
                    "source_url": entry.source_url,
                    "pdf_url": entry.pdf_url or "",
                    "file_path": str(entry.file_path or ""),
                    "status": entry.status,
                    "note": entry.note,
                }
            )


def write_bibliography(entries: list[Entry]) -> None:
    DOC_PATH.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Janus Bibliography",
        "",
        f"Generated from `{MAP_URL}` plus selected 2025-2026 additions from `jp-petit.org/papers/cosmo`.",
        "",
        "PDF files are stored locally under `data/raw/janus_library/` and ignored by Git. The CSV manifest is also stored there.",
        "",
        "## Coverage",
        "",
        f"- Entries: {len(entries)}",
        f"- Downloaded or already present: {sum(entry.status in {'downloaded', 'exists'} for entry in entries)}",
        f"- Missing direct PDF resolver: {sum(entry.status == 'no_pdf_url' for entry in entries)}",
        f"- Failed or non-PDF responses: {sum(entry.status in {'failed', 'not_pdf'} for entry in entries)}",
        "",
        "## Entries",
        "",
        "| ID | Year | Title | Origin | Status | Local file / source |",
        "|---|---:|---|---|---|---|",
    ]

    for entry in entries:
        if entry.file_path and entry.status in {"downloaded", "exists"}:
            target = str(entry.file_path).replace("\\", "/")
        else:
            target = entry.source_url
        lines.append(
            f"| {entry.ref_id} | {entry.year} | {entry.title} | {entry.origin} | {entry.status} | {target} |"
        )

    lines.extend(
        [
            "",
            "## Next Analysis Priority",
            "",
            "1. Extract equations and observables from the 2024-2026 core papers.",
            "2. Reconcile the variable-constants gauge laws with the inferred BAO effective ruler.",
            "3. Separate peer-reviewed papers, preprints, books, and argument/correspondence documents before using them as evidence.",
        ]
    )
    DOC_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    entries = dedupe_entries(parse_map_entries() + EXTRA_ENTRIES)
    for index, entry in enumerate(entries, start=1):
        download_pdf(entry)
        print(f"{index:02d}/{len(entries)} {entry.ref_id} {entry.status}: {entry.title}")
        time.sleep(0.1)

    write_manifest(entries)
    write_bibliography(entries)
    print(f"Wrote {MANIFEST_PATH}")
    print(f"Wrote {DOC_PATH}")


if __name__ == "__main__":
    main()

from __future__ import annotations

import csv
import re
from collections import Counter
from pathlib import Path

from pypdf import PdfReader


MANIFEST_PATH = Path("data/raw/janus_library/manifest.csv")
TEXT_DIR = Path("data/raw/janus_library_text")
REPORT_PATH = Path("outputs/reports/janus_library_keyword_index.md")
CSV_PATH = Path("outputs/reports/janus_library_keyword_index.csv")

KEYWORDS = [
    "DESI",
    "BAO",
    "supernova",
    "redshift",
    "variable constants",
    "speed of light",
    "VSL",
    "CMB",
    "negative mass",
    "negative energy",
    "dark matter",
    "dark energy",
    "galactic",
    "Vlasov",
    "Poisson",
    "plugstar",
    "black hole",
    "Schwarzschild",
    "symplectic",
    "torsor",
    "Sakharov",
    "CPT",
    "Dirac",
]


def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text)


def extract_pdf_text(path: Path) -> tuple[int, str, str]:
    try:
        reader = PdfReader(str(path))
        chunks = [page.extract_text() or "" for page in reader.pages]
        return len(reader.pages), normalize("\n".join(chunks)), ""
    except Exception as exc:  # noqa: BLE001 - indexer should keep going.
        return 0, "", str(exc)


def count_keywords(text: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for keyword in KEYWORDS:
        parts = [re.escape(part) for part in keyword.split()]
        pattern = r"(?<![A-Za-z0-9])" + r"\s+".join(parts) + r"(?![A-Za-z0-9])"
        counts[keyword] = len(re.findall(pattern, text, flags=re.IGNORECASE))
    return counts


def classify(ref_id: str, title: str, counts: dict[str, int]) -> str:
    title_lower = title.lower()
    if "desi" in title_lower or "expansion" in title_lower:
        return "expansion"
    if "variable constants" in title_lower or "inflation" in title_lower:
        return "variable_constants"

    axes = Counter()
    axes["expansion"] = counts["DESI"] + counts["BAO"] + counts["supernova"] + counts["redshift"]
    axes["variable_constants"] = counts["variable constants"] + counts["speed of light"] + counts["VSL"]
    axes["cmb"] = counts["CMB"]
    axes["galaxies"] = counts["dark matter"] + counts["galactic"] + counts["Vlasov"] + counts["Poisson"]
    axes["compact_objects"] = counts["plugstar"] + counts["black hole"] + counts["Schwarzschild"]
    axes["math_symmetry"] = counts["symplectic"] + counts["torsor"] + counts["Sakharov"] + counts["CPT"] + counts["Dirac"]
    axis, score = axes.most_common(1)[0]
    return axis if score > 0 else "uncategorized"


def main() -> None:
    TEXT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, str]] = []
    with MANIFEST_PATH.open(encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["status"] not in {"downloaded", "exists"}:
                continue
            pdf_path = Path(row["file_path"])
            if not pdf_path.exists():
                continue

            pages, text, error = extract_pdf_text(pdf_path)
            text_path = TEXT_DIR / f"{pdf_path.stem}.txt"
            if text:
                text_path.write_text(text, encoding="utf-8")

            counts = count_keywords(text)
            rows.append(
                {
                    "ref_id": row["ref_id"],
                    "year": row["year"],
                    "title": row["title"],
                    "pages": str(pages),
                    "axis": classify(row["ref_id"], row["title"], counts),
                    "text_path": str(text_path if text else ""),
                    "error": error,
                    **{keyword: str(count) for keyword, count in counts.items()},
                }
            )

    fieldnames = [
        "ref_id",
        "year",
        "title",
        "pages",
        "axis",
        "text_path",
        "error",
        *KEYWORDS,
    ]
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    by_axis = Counter(row["axis"] for row in rows)
    lines = [
        "# Janus Library Keyword Index",
        "",
        "This is a machine index over the local PDF library. It is for navigation, not scientific judgment.",
        "",
        f"- Indexed PDFs: {len(rows)}",
        f"- Text extracts: `{TEXT_DIR}`",
        f"- CSV: `{CSV_PATH}`",
        "",
        "## Axis Counts",
        "",
        "| Axis | Count |",
        "|---|---:|",
    ]
    for axis, count in by_axis.most_common():
        lines.append(f"| {axis} | {count} |")

    lines.extend(
        [
            "",
            "## High-Priority Expansion/BAO/Variable-Constants Sources",
            "",
            "| ID | Year | Axis | Title |",
            "|---|---:|---|---|",
        ]
    )

    priority_axes = {"expansion", "variable_constants", "cmb"}
    for row in rows:
        if row["axis"] in priority_axes:
            lines.append(f"| {row['ref_id']} | {row['year']} | {row['axis']} | {row['title']} |")

    lines.extend(
        [
            "",
            "## Next Manual Pass",
            "",
            "1. For each high-priority source, extract exact equations and assumptions.",
            "2. Mark whether it is peer-reviewed, preprint, book, or correspondence/argument.",
            "3. Link each code formula in `src/janus_lab` to a source ID and equation number.",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {REPORT_PATH}")
    print(f"Indexed {len(rows)} PDFs")


if __name__ == "__main__":
    main()

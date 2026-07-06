from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from pypdf import PdfReader


DEFAULT_PDF = Path("C:/Users/alzie/Documents/The_Janus_Cosmological_Model.pdf")
DEFAULT_OUTPUT = Path("outputs/janus_reference")

KEYWORDS = {
    "janus": r"\bjanus\b",
    "z2": r"\bZ\s*2\b|\bZ2\b",
    "sigma": r"\bSigma\b|\bΣ\b",
    "bimetric": r"\bbimetric\b|\bbi[- ]metric\b|\bbim[eé]tr",
    "negative_mass": r"negative mass|masse n[eé]gative|negative energy",
    "positive_mass": r"positive mass|masse positive",
    "throat": r"\bthroat\b|\bgorge\b",
    "wormhole": r"\bwormhole\b|\bbridge\b|\btunnel\b",
    "orientation": r"orientation|inorientable|non[- ]orientable|inversion",
    "time_reversal": r"time reversal|opposite arrows of time|inversion du temps",
    "schwarzschild": r"Schwarzschild",
    "horizon": r"\bhorizon\b",
    "junction": r"junction|jonction|Israel",
    "extrinsic_curvature": r"extrinsic curvature|courbure extrins[eè]que|K_ab|K_\{ab\}",
    "scalar_curvature": r"scalar curvature|courbure scalaire|R\[h\]|Ricci",
    "counterterm": r"counterterm|contre[- ]terme|GHY|Gibbons",
}

EQUATION_LABEL_RE = re.compile(r"\((\d+(?:\.\d+)+)\)")


@dataclass(frozen=True)
class TextQuality:
    score: float
    replacement_ratio: float
    is_searchable: bool


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def normalize_text(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def assess_text_quality(text: str) -> TextQuality:
    if not text:
        return TextQuality(score=0.0, replacement_ratio=0.0, is_searchable=False)
    replacement_ratio = text.count("\ufffd") / max(len(text), 1)
    useful = sum(ch.isalnum() or ch in " .,;:!?()[]{}+-=*/_'\"" for ch in text)
    score = useful / max(len(text), 1)
    is_searchable = len(text) >= 80 and replacement_ratio < 0.02 and score >= 0.65
    return TextQuality(score=round(score, 4), replacement_ratio=round(replacement_ratio, 4), is_searchable=is_searchable)


def keyword_hits(text: str) -> list[str]:
    return [
        name
        for name, pattern in KEYWORDS.items()
        if re.search(pattern, text, flags=re.IGNORECASE)
    ]


def equation_labels(text: str) -> list[str]:
    return sorted(set(EQUATION_LABEL_RE.findall(text)))


def parse_page_spec(spec: str) -> list[int]:
    pages: set[int] = set()
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            start, end = [int(item) for item in part.split("-", 1)]
            pages.update(range(start, end + 1))
        else:
            pages.add(int(part))
    return sorted(page for page in pages if page > 0)


def find_pdftoppm() -> str | None:
    candidates = [
        "C:/Users/alzie/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/poppler/Library/bin/pdftoppm.exe",
        shutil.which("pdftoppm"),
    ]
    for candidate in candidates:
        if candidate and Path(candidate).exists():
            return candidate
    return None


def render_pages(pdf_path: Path, output_dir: Path, pages: Iterable[int], dpi: int) -> list[str]:
    pdftoppm = find_pdftoppm()
    if not pdftoppm:
        return []
    render_dir = output_dir / "rendered_pages"
    render_dir.mkdir(parents=True, exist_ok=True)
    written: list[str] = []
    for page in pages:
        prefix = render_dir / f"page_{page:03d}"
        subprocess.run(
            [pdftoppm, "-png", "-r", str(dpi), "-f", str(page), "-l", str(page), str(pdf_path), str(prefix)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        written.extend(str(path) for path in sorted(render_dir.glob(f"page_{page:03d}-*.png")))
    return written


def find_tesseract() -> str | None:
    candidates = [
        shutil.which("tesseract"),
        "C:/Program Files/Tesseract-OCR/tesseract.exe",
        "C:/Program Files (x86)/Tesseract-OCR/tesseract.exe",
    ]
    for candidate in candidates:
        if candidate and Path(candidate).exists():
            return candidate
    return None


def ocr_page(pdf_path: Path, page_number: int, dpi: int, lang: str) -> str:
    pdftoppm = find_pdftoppm()
    tesseract = find_tesseract()
    if not pdftoppm or not tesseract:
        return ""
    with tempfile.TemporaryDirectory() as temp_dir:
        prefix = Path(temp_dir) / "page"
        subprocess.run(
            [pdftoppm, "-png", "-r", str(dpi), "-f", str(page_number), "-l", str(page_number), str(pdf_path), str(prefix)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        images = sorted(Path(temp_dir).glob("page-*.png"))
        if not images:
            return ""
        output_base = Path(temp_dir) / "ocr"
        subprocess.run(
            [tesseract, str(images[0]), str(output_base), "-l", lang, "--psm", "6"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return normalize_text((output_base.with_suffix(".txt")).read_text(encoding="utf-8", errors="replace"))


def build_reference(
    pdf_path: Path,
    output_dir: Path,
    render_spec: str | None = None,
    dpi: int = 160,
    ocr: bool = False,
    ocr_lang: str = "eng",
    pages: str | None = None,
) -> dict:
    reader = PdfReader(str(pdf_path))
    output_dir.mkdir(parents=True, exist_ok=True)
    pages_path = output_dir / "pages.jsonl"
    map_path = output_dir / "page_map.csv"
    keyword_path = output_dir / "keyword_index.md"
    manifest_path = output_dir / "manifest.json"
    readme_path = output_dir / "README.md"

    keyword_index: dict[str, list[int]] = {key: [] for key in KEYWORDS}
    page_rows: list[dict] = []
    selected_pages = set(parse_page_spec(pages)) if pages else None

    with pages_path.open("w", encoding="utf-8") as pages_file:
        for idx, page in enumerate(reader.pages, start=1):
            if selected_pages is not None and idx not in selected_pages:
                continue
            text = normalize_text(page.extract_text() or "")
            quality = assess_text_quality(text)
            extraction_method = "native"
            if ocr and not quality.is_searchable:
                ocr_text = ocr_page(pdf_path, idx, dpi, ocr_lang)
                ocr_quality = assess_text_quality(ocr_text)
                if len(ocr_text) > len(text) or ocr_quality.score > quality.score:
                    text = ocr_text
                    quality = ocr_quality
                    extraction_method = "ocr"
            hits = keyword_hits(text) if quality.is_searchable else []
            equations = equation_labels(text) if quality.is_searchable else []
            for hit in hits:
                keyword_index[hit].append(idx)
            record = {
                "page": idx,
                "text_quality_score": quality.score,
                "replacement_ratio": quality.replacement_ratio,
                "is_searchable": quality.is_searchable,
                "extraction_method": extraction_method,
                "keyword_hits": hits,
                "equation_labels": equations,
                "preview": text[:240],
                "text": text if quality.is_searchable else "",
            }
            pages_file.write(json.dumps(record, ensure_ascii=False) + "\n")
            page_rows.append(record)

    with map_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "page",
                "is_searchable",
                "extraction_method",
                "text_quality_score",
                "replacement_ratio",
                "keyword_hits",
                "preview",
            ],
        )
        writer.writeheader()
        for row in page_rows:
            writer.writerow(
                {
                    "page": row["page"],
                    "is_searchable": row["is_searchable"],
                    "extraction_method": row["extraction_method"],
                    "text_quality_score": row["text_quality_score"],
                    "replacement_ratio": row["replacement_ratio"],
                    "keyword_hits": ",".join(row["keyword_hits"]),
                    "preview": row["preview"],
                }
            )

    rendered_pages = render_pages(pdf_path, output_dir, parse_page_spec(render_spec), dpi) if render_spec else []
    formula_path = output_dir / "formula_index.md"
    formula_lines = ["# Janus Reference Formula Index", ""]
    for row in page_rows:
        if row["equation_labels"]:
            formula_lines.append(
                f"- page {row['page']}: "
                + ", ".join(f"`{label}`" for label in row["equation_labels"])
            )
    formula_path.write_text("\n".join(formula_lines) + "\n", encoding="utf-8")
    searchable_pages = [row["page"] for row in page_rows if row["is_searchable"]]
    needs_ocr_pages = [row["page"] for row in page_rows if not row["is_searchable"]]
    manifest = {
        "source_pdf": str(pdf_path),
        "sha256": sha256_file(pdf_path),
        "page_count": len(reader.pages),
        "processed_page_count": len(page_rows),
        "searchable_page_count": len(searchable_pages),
        "ocr_enabled": ocr,
        "tesseract_available": find_tesseract() is not None,
        "needs_ocr_page_count": len(needs_ocr_pages),
        "outputs": {
            "pages_jsonl": str(pages_path),
            "page_map_csv": str(map_path),
            "keyword_index_md": str(keyword_path),
            "formula_index_md": str(formula_path),
            "readme_md": str(readme_path),
            "rendered_pages": rendered_pages,
        },
        "keyword_page_counts": {key: len(value) for key, value in keyword_index.items()},
        "ocr_recommended": bool(needs_ocr_pages),
        "needs_ocr_pages_sample": needs_ocr_pages[:40],
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8")

    lines = ["# Janus Reference Keyword Index", ""]
    for key, pages in keyword_index.items():
        page_text = ", ".join(str(page) for page in pages[:80]) if pages else "none"
        suffix = "" if len(pages) <= 80 else f" ... (+{len(pages) - 80})"
        lines.append(f"- `{key}`: {page_text}{suffix}")
    keyword_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    readme_path.write_text(
        "\n".join(
            [
                "# Janus PDF Reference",
                "",
                "Generated by `scripts/process_janus_reference_pdf.py`.",
                "",
                "- `manifest.json`: source hash, page count, OCR status.",
                "- `pages.jsonl`: one JSON record per page; `text` is blank when native text is not reliable.",
                "- `page_map.csv`: quick spreadsheet-friendly page status.",
                "- `keyword_index.md`: keyword to page map for fast navigation.",
                "- `formula_index.md`: equation labels detected per page.",
                "- `rendered_pages/`: optional PNG pages created with `--render-pages`.",
                "",
                "Run:",
                "",
                "```powershell",
                "python scripts/process_janus_reference_pdf.py --ocr --render-pages 1,35,85",
                "```",
                "",
                "If most pages are `needs_ocr`, install Tesseract/OCR separately before relying on text search.",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description="Prepare searchable local reference artifacts for the Janus PDF.")
    parser.add_argument("--pdf", type=Path, default=DEFAULT_PDF)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--render-pages", default=None, help="Optional page spec, e.g. '1,35,80-82'.")
    parser.add_argument("--dpi", type=int, default=160)
    parser.add_argument("--ocr", action="store_true", help="OCR pages whose native text layer is not reliable.")
    parser.add_argument("--ocr-lang", default="eng")
    parser.add_argument("--pages", default=None, help="Optional page spec to process only a subset, e.g. '1-10,35'.")
    args = parser.parse_args()
    manifest = build_reference(args.pdf, args.output, args.render_pages, args.dpi, args.ocr, args.ocr_lang, args.pages)
    print(json.dumps(manifest, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()

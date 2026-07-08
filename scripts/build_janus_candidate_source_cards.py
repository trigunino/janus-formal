from __future__ import annotations

import csv
import re
from pathlib import Path

from ftfy import fix_text
import fitz


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "data" / "raw" / "janus_library_candidates" / "candidate_new_manifest.csv"
PDF_DIR = ROOT / "data" / "raw" / "janus_library_candidates"
TEXT_DIR = ROOT / "data" / "raw" / "janus_library_candidate_text"
CARD_DIR = ROOT / "docs" / "source_cards_candidates"
MASTER_PATH = ROOT / "docs" / "janus_candidate_knowledge_base.md"

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

LOGIC_BY_AXIS = {
    "bimetric_geodesics": "Use the two-sector geometry and coupled field equations as the primary mechanism. Signed-mass interaction laws should follow from the bimetric setup, not be added by hand.",
    "expansion": "Use the Janus exact expansion/redshift machinery and compare to supernova and background expansion observables without silently importing Lambda-CDM closures.",
    "galaxies": "Use positive/negative sector interaction, lensing and kinetic/VLS arguments to replace standard dark-matter phenomenology in galaxy and structure contexts.",
    "compact_objects": "Treat this as a compact-object/singularity critique branch rather than a background-cosmology anchor.",
    "math_symmetry": "Treat this as a symmetry/Sakharov/PT/CPT/group-structure branch that informs model interpretation before direct observational claims.",
}


def load_rows() -> list[dict[str, str]]:
    with MANIFEST_PATH.open(encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def extract_pdf_text(path: Path) -> tuple[int, str]:
    doc = fitz.open(path)
    pages = len(doc)
    text = "\n".join(doc[i].get_text("text") for i in range(pages))
    text = fix_text(text)
    text = text.replace("\x00", " ").replace("\uffff", " ")
    return pages, re.sub(r"\s+", " ", text).strip()


def count_keywords(text: str) -> list[tuple[str, int]]:
    hits: list[tuple[str, int]] = []
    for keyword in KEYWORDS:
        parts = [re.escape(part) for part in keyword.split()]
        pattern = r"(?<![A-Za-z0-9])" + r"\s+".join(parts) + r"(?![A-Za-z0-9])"
        count = len(re.findall(pattern, text, flags=re.IGNORECASE))
        if count:
            hits.append((keyword, count))
    return sorted(hits, key=lambda item: (-item[1], item[0]))[:8]


def equation_markers(text: str, limit: int = 10) -> list[str]:
    pattern = re.compile(r"\b(?:Eq\.?|Eqs\.?|equation|Equation)\s*\(?\s*([0-9]+[a-z]?)", re.IGNORECASE)
    seen: set[str] = set()
    out: list[str] = []
    for match in pattern.finditer(text):
        marker = match.group(0).strip()
        key = marker.lower()
        if key not in seen:
            seen.add(key)
            out.append(marker)
        if len(out) >= limit:
            break
    return out


def snippets(text: str, terms: list[str], limit: int = 2, window: int = 90) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for term in terms:
        for match in re.finditer(re.escape(term), text, flags=re.IGNORECASE):
            start = max(0, match.start() - window)
            end = min(len(text), match.end() + window)
            snippet = re.sub(r"\s+", " ", text[start:end]).strip()
            if len(snippet) > 220:
                snippet = snippet[:217] + "..."
            key = snippet.lower()
            if key not in seen:
                seen.add(key)
                out.append(snippet)
            if len(out) >= limit:
                return out
    return out


def build_card(row: dict[str, str], text_path: Path, pages: int, text: str) -> str:
    keyword_counts = count_keywords(text)
    keyword_terms = [k for k, _ in keyword_counts]
    equations = equation_markers(text)
    observable_terms = ["supernova", "redshift", "dark matter", "dark energy", "galactic", "VLS", "repeller", "CMB"]
    obs_snips = snippets(text, observable_terms)
    eq_snips = snippets(text, ["Eq.", "Equation"])
    core_snips = snippets(text, keyword_terms or [row["title"]])
    logic = LOGIC_BY_AXIS.get(row["axis"], "Use this as a navigation/source context document until a stronger manual curation pass is done.")
    title_lower = row["title"].lower()
    sample = text[:12000]
    tags = [row["axis"]]
    if "negative mass" in title_lower or "negative energy" in title_lower or "negative mass" in sample.lower() or "negative energy" in sample.lower():
        tags.append("signed_mass_sector")
    if "sakharov" in title_lower or "sakharov" in sample.lower():
        tags.append("sakharov")
    if re.search(r"\b(?:PT|CPT)\b", sample):
        tags.append("pt_cpt")
    if "black hole" in title_lower or "schwarzschild" in title_lower:
        tags.append("compact_object_alternative")
    if "symplectic" in title_lower or "torsor" in title_lower or "symplectic" in sample.lower() or "torsor" in sample.lower():
        tags.append("symmetry_formalism")
    tags = sorted(set(tags))
    rel_text_path = text_path.relative_to(ROOT).as_posix()
    lines = [
        f"# {row['ref_id']} - {row['title']}",
        "",
        "## Metadata",
        "",
        f"- Year: {row['year']}",
        f"- Axis: {row['axis']}",
        f"- Source level: candidate-new imported from extended bibliography pass",
        f"- PDF: `data\\raw\\janus_library_candidates\\{row['file_name']}`",
        f"- Text extract: `{rel_text_path}`",
        f"- Extraction status: ok",
        f"- Kind: {row['kind']}",
        f"- Pages: {pages}",
        "",
        "## Logic Of Thought",
        "",
        logic,
        "",
        f"Tags: `{', '.join(tags)}`",
        "",
        "## Formula And Equation Anchors",
        "",
    ]
    if equations:
        lines.append("Equation markers found automatically:")
        for marker in equations:
            lines.append(f"- `{marker}`")
    else:
        lines.append("- No equation markers auto-detected in this pass.")
    lines.extend(["", "## Core Ideas / Cues", ""])
    if keyword_counts:
        lines.append("Keyword signals: " + ", ".join(f"`{k}`={v}" for k, v in keyword_counts) + ".")
    else:
        lines.append("Keyword signals: none from the standard index list.")
    if core_snips:
        lines.extend(["", "Short source windows for orientation:"])
        for snippet in core_snips:
            lines.append(f"- {snippet}")
    lines.extend(["", "## Observational Hooks", ""])
    if obs_snips:
        for snippet in obs_snips:
            lines.append(f"- {snippet}")
    else:
        lines.append("- No strong observable hook snippet captured in this automatic pass.")
    lines.extend(["", "## Verification Notes", ""])
    if eq_snips:
        lines.append("Short equation/formula windows to check in the PDF:")
        for snippet in eq_snips:
            lines.append(f"- {snippet}")
    else:
        lines.append("- Manual equation/claim verification still needed.")
    lines.extend(["", f"Manual note: {row['note']}"])
    return "\n".join(lines) + "\n"


def main() -> None:
    TEXT_DIR.mkdir(parents=True, exist_ok=True)
    CARD_DIR.mkdir(parents=True, exist_ok=True)
    rows = load_rows()
    master_lines = [
        "# Janus Candidate Knowledge Base",
        "",
        "This file covers only the promoted `candidate-new` documents from the extended bibliography pass.",
        "",
        "| Ref | Year | Axis | Kind | Card | Title |",
        "|---|---:|---|---|---|---|",
    ]
    for row in rows:
        pdf_path = PDF_DIR / row["file_name"]
        pages, text = extract_pdf_text(pdf_path)
        text_path = TEXT_DIR / f"{row['ref_id']}_{pdf_path.stem}.txt"
        text_path.write_text(text, encoding="utf-8")
        card_path = CARD_DIR / f"{row['ref_id']}.md"
        card_path.write_text(build_card(row, text_path, pages, text), encoding="utf-8")
        master_lines.append(
            f"| {row['ref_id']} | {row['year']} | {row['axis']} | {row['kind']} | [card](source_cards_candidates/{row['ref_id']}.md) | {row['title']} |"
        )
    MASTER_PATH.write_text("\n".join(master_lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

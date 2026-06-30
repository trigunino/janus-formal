from __future__ import annotations

import csv
import re
from collections import Counter
from pathlib import Path


MANIFEST_PATH = Path("data/raw/janus_library/manifest.csv")
KEYWORD_INDEX_PATH = Path("outputs/reports/janus_library_keyword_index.csv")
TEXT_DIR = Path("data/raw/janus_library_text")
CARD_DIR = Path("docs/source_cards")
MASTER_PATH = Path("docs/janus_knowledge_base.md")
AGENT_PATH = Path("docs/agent_handoff.md")
COVERAGE_CSV_PATH = Path("outputs/reports/janus_knowledge_coverage.csv")
COVERAGE_MD_PATH = Path("outputs/reports/janus_knowledge_coverage.md")


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

CURATED_FORMULAS = {
    "M15": [
        "`G(+) = chi [T(+) + sqrt(-g(-)/-g(+)) T(-)]` (Eqs. 4a-4b)",
        "`G(-) = -chi [sqrt(-g(+)/-g(-)) T(+) + T(-)]` (Eqs. 4a-4b)",
        "`rho(+)>0, p(+)>0; rho(-)<0, p(-)<0` (Eq. 5)",
        "Double Newtonian limit around two Lorentz metrics (Eq. 6)",
    ],
    "M18": [
        "`m = 5 log10[z + z^2(1-q0)/(1+q0 z + sqrt(1+2q0z))] + cst` (Eq. 5)",
        "`q0 = -0.087 +/- 0.015` from the SN fit (Eq. 6)",
        "`a(u)` proportional to `cosh(u)^2`, with parametric `t(u)` (Eq. 10)",
        "`q = -1/(2 sinh(u)^2)` and open marker `r = sinh(2(u0-u_e))` (Eqs. 13, 17)",
    ],
    "M22": [
        "`|rho(-)| > rho(+) => t_J(-) << t_J(+)` (Eq. 1 in the current traceability pass)",
    ],
    "M30": [
        "Single-field signed-mass failure is analyzed before the bimetric replacement (Eqs. 75-79)",
        "Two metric/geodesic families replace the Bondi one-metric setup (Sect. 9)",
        "`G = chi[T + b^2 Tbar]`; `Gbar = -chi[T + bbar^2 Tbar]` (Eqs. 105a-105b)",
        "Newtonian interaction laws and local GR recovery are stated after Eq. 106",
    ],
    "M31": [
        "Janus symplectic group action on torsors classifies energy, momentum and charge transformations",
    ],
    "X2025-bimetric-hal": [
        "HAL mirror of the bimetric Sakharov model; use with M30 as the published anchor",
    ],
    "X2025-kinetic-galactic": [
        "Vlasov/Poisson construction for galaxy dynamics; Poisson equation is tracked in `source_traceability.md`",
    ],
    "X2025-symplectic-hal": [
        "HAL mirror/continuation of the Janus symplectic group work; use with M31 as the published anchor",
    ],
    "X2026-variable-constants": [
        "`c_hat` proportional to `1/sqrt(a)`; `h_hat` proportional to `a^(3/2)` (Eq. 40)",
        "`G_hat` proportional to `1/a`; `e_hat` proportional to `sqrt(a)`; `m_hat` proportional to `a` (Eq. 40)",
        "Characteristic lengths scale as `a`; characteristic times scale as `a^(3/2)`",
    ],
    "X2026-expansion-desi": [
        "Reuses the exact Janus expansion route and frames the DESI tension as a target observable",
        "FLRW setup and compatibility condition around Eqs. 25-30 need manual equation validation",
    ],
}

CURATED_LOGIC = {
    "M15": [
        "Start from the Bondi one-metric runaway problem, then remove it by assigning the two mass signs to two coupled metric/geodesic families.",
        "Use the Newtonian limit only after the bimetric field equations are fixed, so the attraction/repulsion rules are consequences rather than assumptions.",
    ],
    "M18": [
        "Use the exact Janus expansion solution as the geometry, then fit the SN magnitude-redshift law with a single shape parameter `q0` plus nuisance offset.",
        "Keep the open-distance mapping explicit; BAO use requires checking that the same ruler assumptions are still valid.",
    ],
    "M30": [
        "Modernize the bimetric construction through Sakharov's twin-universe idea and stationary mixed equations.",
        "Show why single-metric signed-mass GR fails, then recover local GR when one sector is absent.",
    ],
    "M31": [
        "Treat matter/antimatter and energy-sector transformations as a symmetry/torsor problem before attaching physical interpretation.",
    ],
    "X2025-kinetic-galactic": [
        "Model galaxy dynamics as a kinetic/gravitational distribution problem rather than adding particle dark matter by default.",
    ],
    "X2026-expansion-desi": [
        "Treat DESI as a discriminator for the Janus exact expansion solution, but separate the expansion law from the BAO ruler calibration problem.",
    ],
    "X2026-variable-constants": [
        "Use a variable-constants gauge to revisit early-universe horizon/ruler problems before comparing calibrated observables.",
        "Eq. 40 is a hypothesis source for the BAO effective-ruler clue, not yet a derived BAO formula.",
    ],
}

AXIS_OVERRIDES = {
    "M15": "bimetric_geodesics",
    "M30": "bimetric_geodesics",
    "X2025-bimetric-hal": "bimetric_geodesics",
    "X2026-expansion-desi": "expansion",
}

LOGIC_BY_AXIS = {
    "bimetric_geodesics": "Formalize the two-sector geometry first: signed masses/energies live on distinct metric geodesic families, with coupled field equations determining the Newtonian interaction laws.",
    "expansion": "Use the exact Janus expansion/redshift machinery, then compare against SNe, BAO, DESI and CMB-derived observables without importing Lambda-CDM assumptions silently.",
    "variable_constants": "Change the physical gauge/constants regime to address horizon, early-universe and ruler-calibration problems before fitting observables.",
    "cmb": "Connect negative-sector structure and early-universe assumptions to CMB fluctuation observables.",
    "galaxies": "Use positive/negative sector interactions or kinetic theory to replace particle dark matter in galaxy and large-scale-structure phenomenology.",
    "compact_objects": "Test whether singular black-hole/horizon assumptions are internally inconsistent and whether plugstar-like alternatives follow from Janus geometry.",
    "math_symmetry": "Formalize the symmetry group, torsor action and matter/antimatter sector transformations before deriving physical claims.",
    "uncategorized": "Automatic keyword routing is weak here; use the title, PDF and search tool before assigning this source to a model component.",
}

SOURCE_LEVEL_OVERRIDES = {
    "M15": "published Janus source; equation-level anchor for coupled field equations",
    "M18": "published Janus source; equation-level anchor for SN/open-distance formulas",
    "M30": "peer-reviewed 2024 EPJC source; modern bimetric/geodesic anchor",
    "M31": "peer-reviewed 2024 EPJC source; modern symmetry anchor",
    "X2025-bimetric-hal": "HAL/local mirror of the bimetric work; use M30 as primary anchor",
    "X2025-symplectic-hal": "HAL/local mirror of the symmetry work; use M31 as primary anchor",
    "X2026-expansion-desi": "recent author document; use for hypotheses until independently validated",
    "X2026-variable-constants": "recent author document; use for hypotheses until independently validated",
    "X2026-questionable-black-holes": "Journal of Modern Physics 2026 compact-object source; not a core lensing/S8 proof anchor",
    "X2026-complex-reality": "recent author document; symmetry/complex-reality roadmap, not a primary cosmology proof anchor",
    "X2025-technical-book": "book/technical synthesis; useful for navigation, not a primary equation anchor",
}


def load_csv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def ref_from_text_path(path_text: str) -> str:
    name = Path(path_text).name
    return name.split("_", 1)[0]


def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def safe_filename(ref_id: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "-", ref_id).strip("-")


def source_level(row: dict[str, str]) -> str:
    ref_id = row["ref_id"]
    if ref_id in SOURCE_LEVEL_OVERRIDES:
        return SOURCE_LEVEL_OVERRIDES[ref_id]
    if ref_id.startswith("M"):
        return "map-listed Janus publication; journal/status metadata should be verified before citation"
    return "recent add-on source; verify publication status before using as evidence"


def display_axis(row: dict[str, str]) -> str:
    return AXIS_OVERRIDES.get(row["ref_id"], row.get("axis", "uncategorized"))


def top_keywords(row: dict[str, str], limit: int = 8) -> list[tuple[str, int]]:
    counts = []
    for keyword in KEYWORDS:
        try:
            count = int(row.get(keyword, "0") or 0)
        except ValueError:
            count = 0
        if count:
            counts.append((keyword, count))
    return sorted(counts, key=lambda item: (-item[1], item[0]))[:limit]


def text_for(row: dict[str, str]) -> str:
    path_text = row.get("text_path", "")
    if not path_text:
        return ""
    path = Path(path_text)
    if not path.exists():
        path = TEXT_DIR / Path(path_text).name
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8", errors="replace")


def equation_markers(text: str, limit: int = 12) -> list[str]:
    pattern = re.compile(r"\b(?:Eq\.?|Eqs\.?|equation|Equation)\s*\(?\s*([0-9]+[a-z]?(?:\s*[-,/]\s*[0-9]+[a-z]?|\s*(?:and|to)\s*[0-9]+[a-z]?)*)\s*\)?")
    markers: list[str] = []
    seen: set[str] = set()
    for match in pattern.finditer(text):
        marker = normalize(match.group(0))
        marker = marker[:80]
        key = marker.lower()
        if key not in seen:
            seen.add(key)
            markers.append(marker)
        if len(markers) >= limit:
            break
    return markers


def looks_readable(snippet: str) -> bool:
    bad_markers = ["\ufffd", "Ã", "Â", "â", "ï", "Î", "ð"]
    return not any(marker in snippet for marker in bad_markers)


def short_snippets(text: str, terms: list[str], limit: int = 2, window: int = 90) -> list[str]:
    snippets: list[str] = []
    seen: set[str] = set()
    for term in terms:
        pattern = re.compile(re.escape(term), re.IGNORECASE)
        for match in pattern.finditer(text):
            start = max(0, match.start() - window)
            end = min(len(text), match.end() + window)
            snippet = normalize(text[start:end])
            if len(snippet) > 220:
                snippet = snippet[:217].rstrip() + "..."
            if not looks_readable(snippet):
                continue
            key = snippet.lower()
            if key not in seen:
                seen.add(key)
                snippets.append(snippet)
            if len(snippets) >= limit:
                return snippets
    return snippets


def logic_tags(row: dict[str, str]) -> list[str]:
    title = row["title"].lower()
    axis = display_axis(row)
    tags = [axis]
    if "negative" in title or int(row.get("negative mass", "0") or 0) or int(row.get("negative energy", "0") or 0):
        tags.append("signed_mass_sector")
    if "bimetric" in title or int(row.get("Sakharov", "0") or 0):
        tags.append("bimetric_geometry")
    if "variable" in title or int(row.get("variable constants", "0") or 0) or int(row.get("VSL", "0") or 0):
        tags.append("variable_constants")
    if "black hole" in title or int(row.get("black hole", "0") or 0) or int(row.get("plugstar", "0") or 0):
        tags.append("compact_object_alternative")
    if "symplectic" in title or int(row.get("symplectic", "0") or 0) or int(row.get("torsor", "0") or 0):
        tags.append("symmetry_formalism")
    if "desi" in title or int(row.get("DESI", "0") or 0) or int(row.get("BAO", "0") or 0):
        tags.append("observational_expansion_test")
    return list(dict.fromkeys(tags))


def card_lines(row: dict[str, str], manifest_row: dict[str, str]) -> list[str]:
    ref_id = row["ref_id"]
    text = text_for(row)
    keywords = top_keywords(row)
    markers = equation_markers(text)
    formulas = CURATED_FORMULAS.get(ref_id, [])
    observable_terms = ["DESI", "BAO", "supernova", "CMB", "redshift", "rotation", "galactic", "black hole", "M87", "Sgr A", "JWST"]
    formula_terms = ["Eq.", "equation", "geodesic", "metric", "Poisson", "Vlasov", "sinh", "cosh", "sqrt", "Schwarzschild"]
    idea_terms = ["negative mass", "negative energy", "bimetric", "symmetry", "torsor", "variable constants", "dark matter", "dark energy", "CPT", "Dirac"]

    lines = [
        f"# {ref_id} - {manifest_row['title']}",
        "",
        "## Metadata",
        "",
        f"- Year: {manifest_row['year']}",
        f"- Axis: {display_axis(row)}",
        f"- Source level: {source_level(row)}",
        f"- PDF: `{manifest_row.get('file_path', '')}`",
        f"- Text extract: `{row.get('text_path', '')}`",
        f"- Extraction status: {'ok' if len(text) > 200 else 'weak-or-empty'}",
        "",
        "## Logic Of Thought",
        "",
        LOGIC_BY_AXIS.get(display_axis(row), LOGIC_BY_AXIS["uncategorized"]),
        "",
        "Tags: " + ", ".join(f"`{tag}`" for tag in logic_tags(row)),
        "",
    ]
    if ref_id in CURATED_LOGIC:
        lines.extend(["Curated logic anchors:", ""])
        lines.extend(f"- {item}" for item in CURATED_LOGIC[ref_id])
        lines.append("")
    lines.extend(
        [
        "## Formula And Equation Anchors",
        "",
        ]
    )
    if formulas:
        lines.extend(f"- {formula}" for formula in formulas)
    else:
        lines.append("- No curated formula yet. Use equation markers and PDF verification before formal use.")
    if markers:
        lines.extend(["", "Equation markers found automatically:"])
        lines.extend(f"- `{marker}`" for marker in markers)
    lines.extend(
        [
            "",
            "## Core Ideas / Cues",
            "",
        ]
    )
    if keywords:
        lines.append("Keyword signals: " + ", ".join(f"`{keyword}`={count}" for keyword, count in keywords) + ".")
    else:
        lines.append("No strong keyword signal in the automatic index.")
    snippets = short_snippets(text, idea_terms, limit=2)
    if snippets:
        lines.extend(["", "Short source windows for orientation:"])
        lines.extend(f"- {snippet}" for snippet in snippets)
    lines.extend(["", "## Observational Hooks", ""])
    obs = [(keyword, count) for keyword, count in keywords if keyword in {"DESI", "BAO", "supernova", "redshift", "CMB", "galactic", "dark matter", "black hole"}]
    if obs:
        lines.append(", ".join(f"`{keyword}`={count}" for keyword, count in obs) + ".")
    else:
        lines.append("No direct observational hook detected automatically.")
    obs_snippets = short_snippets(text, observable_terms, limit=2)
    if obs_snippets:
        lines.extend(["", "Short observable windows:"])
        lines.extend(f"- {snippet}" for snippet in obs_snippets)
    formula_snippets = short_snippets(text, formula_terms, limit=2)
    lines.extend(["", "## Verification Notes", ""])
    if formula_snippets:
        lines.append("Short equation/formula windows to check in the PDF:")
        lines.extend(f"- {snippet}" for snippet in formula_snippets)
    else:
        lines.append("No reliable equation/formula window extracted automatically.")
    lines.extend(
        [
            "",
            "Manual status: automatic first-pass card. Treat as navigation unless formulas are listed as curated above or verified in the PDF.",
            "",
        ]
    )
    return lines


def coverage_status(row: dict[str, str], text: str) -> str:
    has_curated = row["ref_id"] in CURATED_FORMULAS
    has_keywords = bool(top_keywords(row))
    has_text = len(text) > 200
    if has_curated and has_text:
        return "curated-anchor"
    if has_text and has_keywords:
        return "auto-indexed"
    if has_text:
        return "text-only"
    return "weak-extraction"


def write_agent_handoff() -> None:
    lines = [
        "# Janus Agent Handoff",
        "",
        "Purpose: give any future AI agent a clean starting point for Janus work without rereading the whole corpus blindly.",
        "",
        "## Start Here",
        "",
        "1. Read `docs/janus_knowledge_base.md` for the map.",
        "2. Open the relevant card in `docs/source_cards/`.",
        "3. Check `docs/verified_formula_register.md` before relying on any formula.",
        "4. Follow `docs/toolchain.md` for source -> formalization -> code -> data work.",
        "5. Use `python scripts/search_janus_library.py \"query\" --ref M18` for source-local checks.",
        "6. Verify every new equation against the local PDF before promoting it to `docs/source_traceability.md` or code.",
        "",
        "## Evidence Rules",
        "",
        "- Keep source ID, equation number and document status together.",
        "- Do not mix peer-reviewed anchors, HAL mirrors, books and author documents as if they had the same evidential weight.",
        "- Mark phenomenological fits separately from Janus-derived formulas.",
        "- If Janus is used as an axiom, state that explicitly and search for the missing map from Janus assumptions to observables.",
        "",
        "## Current High-Value Anchors",
        "",
        "- `M15`: coupled field equations and signed-mass interaction logic.",
        "- `M18`: SN/open-distance formulas and exact expansion parameterization.",
        "- `M30`: modern bimetric/geodesic formulation.",
        "- `M31`: symmetry/torsor formalism.",
        "- `X2026-variable-constants`: variable-constants hypothesis, especially Eq. 40.",
        "- `X2026-expansion-desi`: current DESI-oriented expansion target.",
        "",
        "## Known Weak Point",
        "",
        "`M26` currently has a weak/empty text extraction. Use the PDF directly before relying on that card.",
        "",
    ]
    AGENT_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    manifest_rows = load_csv(MANIFEST_PATH)
    keyword_rows = load_csv(KEYWORD_INDEX_PATH)
    manifest_by_ref = {row["ref_id"]: row for row in manifest_rows}
    keyword_by_ref = {row["ref_id"]: row for row in keyword_rows}

    CARD_DIR.mkdir(parents=True, exist_ok=True)
    COVERAGE_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)

    coverage_rows: list[dict[str, str]] = []
    for ref_id, manifest_row in manifest_by_ref.items():
        row = keyword_by_ref.get(ref_id)
        if row is None:
            row = {"ref_id": ref_id, "year": manifest_row["year"], "title": manifest_row["title"], "axis": "uncategorized", "text_path": ""}
        text = text_for(row)
        card_path = CARD_DIR / f"{safe_filename(ref_id)}.md"
        card_path.write_text("\n".join(card_lines(row, manifest_row)), encoding="utf-8")
        coverage_rows.append(
            {
                "ref_id": ref_id,
                "year": manifest_row["year"],
                "title": manifest_row["title"],
                "axis": display_axis(row),
                "card_path": str(card_path),
                "text_chars": str(len(text)),
                "top_keywords": "; ".join(f"{keyword}:{count}" for keyword, count in top_keywords(row, limit=5)),
                "equation_markers": str(len(equation_markers(text))),
                "curated_formulas": str(len(CURATED_FORMULAS.get(ref_id, []))),
                "status": coverage_status(row, text),
            }
        )

    with COVERAGE_CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        fieldnames = [
            "ref_id",
            "year",
            "title",
            "axis",
            "card_path",
            "text_chars",
            "top_keywords",
            "equation_markers",
            "curated_formulas",
            "status",
        ]
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(coverage_rows)

    by_axis = Counter(row["axis"] for row in coverage_rows)
    by_status = Counter(row["status"] for row in coverage_rows)
    master_lines = [
        "# Janus Knowledge Base",
        "",
        "Machine-generated source map over the local Janus PDF corpus. It stores formulas, idea cues, reasoning logic and observable hooks in a form usable by future agents.",
        "",
        "Important: this is a navigation and traceability layer. Exact formulas must still be checked against PDFs before they become code or scientific claims.",
        "",
        "## Coverage",
        "",
        f"- Manifest sources: {len(manifest_rows)}",
        f"- Source cards: {len(coverage_rows)}",
        f"- Coverage CSV: `{COVERAGE_CSV_PATH}`",
        f"- Agent workflow: `{AGENT_PATH}`",
        "",
        "### By Axis",
        "",
        "| Axis | Count |",
        "|---|---:|",
    ]
    for axis, count in by_axis.most_common():
        master_lines.append(f"| {axis} | {count} |")
    master_lines.extend(["", "### By Status", "", "| Status | Count |", "|---|---:|"])
    for status, count in by_status.most_common():
        master_lines.append(f"| {status} | {count} |")
    master_lines.extend(
        [
            "",
            "## Source Cards",
            "",
            "| ID | Year | Axis | Status | Card | Title |",
            "|---|---:|---|---|---|---|",
        ]
    )
    for row in coverage_rows:
        master_lines.append(
            f"| {row['ref_id']} | {row['year']} | {row['axis']} | {row['status']} | "
            f"[card](source_cards/{safe_filename(row['ref_id'])}.md) | {row['title']} |"
        )
    master_lines.extend(
        [
            "",
            "## Highest Priority Manual Checks",
            "",
            "1. Use `docs/verified_formula_register.md` as the promoted source for checked formulas.",
            "2. Repair or manually summarize weak extraction cards, especially `M26`.",
            "3. Verify any new formula against the PDF before adding it to code or `docs/source_traceability.md`.",
            "",
        ]
    )
    MASTER_PATH.write_text("\n".join(master_lines), encoding="utf-8")

    coverage_lines = [
        "# Janus Knowledge Coverage",
        "",
        f"- Manifest sources: {len(manifest_rows)}",
        f"- Keyword rows: {len(keyword_rows)}",
        f"- Source cards written: {len(coverage_rows)}",
        "",
        "## Status Counts",
        "",
        "| Status | Count |",
        "|---|---:|",
    ]
    for status, count in by_status.most_common():
        coverage_lines.append(f"| {status} | {count} |")
    coverage_lines.extend(["", "## Weak Or Low-Signal Sources", "", "| ID | Text chars | Status | Title |", "|---|---:|---|---|"])
    for row in coverage_rows:
        if row["status"] in {"weak-extraction", "text-only"}:
            coverage_lines.append(f"| {row['ref_id']} | {row['text_chars']} | {row['status']} | {row['title']} |")
    coverage_lines.append("")
    COVERAGE_MD_PATH.write_text("\n".join(coverage_lines), encoding="utf-8")

    write_agent_handoff()

    print(f"Wrote {len(coverage_rows)} source cards to {CARD_DIR}")
    print(f"Wrote {MASTER_PATH}")
    print(f"Wrote {AGENT_PATH}")
    print(f"Wrote {COVERAGE_CSV_PATH}")
    print(f"Wrote {COVERAGE_MD_PATH}")


if __name__ == "__main__":
    main()

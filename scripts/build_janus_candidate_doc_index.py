from __future__ import annotations

import csv
from dataclasses import dataclass
from pathlib import Path

from ftfy import fix_text
import fitz


ROOT = Path(__file__).resolve().parents[1]
CANDIDATE_DIR = ROOT / "data" / "raw" / "janus_library_candidates"
REPORT_MD = ROOT / "outputs" / "reports" / "janus_candidate_doc_index_2026-07-08.md"
REPORT_CSV = ROOT / "outputs" / "reports" / "janus_candidate_doc_index_2026-07-08.csv"


@dataclass(frozen=True)
class Spec:
    file_name: str
    title: str
    year: int
    axis: str
    status: str
    existing_ref: str = ""
    kind: str = ""
    useful_for: str = ""
    note: str = ""


SPECS = [
    Spec("Anewinterpretationofthecosmicacceleration.pdf", "A new interpretation of the cosmic acceleration", 2015, "expansion", "candidate-new", kind="preprint", useful_for="SN Ia reanalysis; exact Janus expansion fit", note="Direct observation-facing acceleration paper."),
    Spec("Can negative mass be considered in General Relativity.pdf", "Can negative mass be considered in General Relativity ?", 2014, "bimetric_geodesics", "candidate-new", kind="preprint", useful_for="Foundational bimetric replacement of Bondi runaway", note="Useful for the negative-mass interaction law and Newtonian limit."),
    Spec("Janus Model Mathematically and Physically Consistent.pdf", "Janus Cosmological Model Mathematically and Physically Consistent", 2024, "bimetric_geodesics", "candidate-new", kind="HAL preprint", useful_for="2024 consistency synthesis; bridge to paper-native branch", note="Not yet in main manifest; likely should become an extended2026 anchor."),
    Spec("Janus-acceleration_cosmic_expansion.pdf", "Janus, the only cosmological model that explains the acceleration of cosmic expansion", 2022, "expansion", "duplicate-main", existing_ref="X2022-hal-acceleration-cosmic-expansion", kind="HAL preprint", useful_for="Background expansion / DESI / SN branch", note="Already in main library."),
    Spec("JPP2008-matter-antimatter-geometrization-1.pdf", "Geometrization of matter and antimatter ... 1", 2008, "math_symmetry", "near-duplicate-main", existing_ref="M11", kind="series preprint", useful_for="Group/coadjoint machinery; charges as momentum components", note="Part of the broader matter-antimatter geometry series already represented by M11."),
    Spec("JPP2008-matter-antimatter-geometrization-2.pdf", "Geometrization of matter and antimatter ... 2", 2008, "math_symmetry", "near-duplicate-main", existing_ref="M11", kind="series preprint", useful_for="Dirac antimatter geometric description", note="Companion to M11-style symmetry material."),
    Spec("JPP2008-matter-antimatter-geometrization-3.pdf", "Geometrization of matter and antimatter ... 3", 2008, "math_symmetry", "near-duplicate-main", existing_ref="M11", kind="series preprint", useful_for="PT/CPT interpretation in dynamic-group language", note="Relevant for PT-oriented branches."),
    Spec("JPP2008-matter-antimatter-geometrization-4.pdf", "Geometrization of matter and antimatter ... 4: The Twin group", 2008, "math_symmetry", "near-duplicate-main", existing_ref="M11", kind="series preprint", useful_for="Twin-group construction; positive/negative mass segregation", note="Useful for global symmetry genealogy."),
    Spec("JPP2014-AstrophysSpaceSci.pdf", "Negative mass hypothesis in cosmology and the nature of dark energy", 2014, "galaxies", "duplicate-main", existing_ref="M13", kind="journal", useful_for="Dark-energy replacement via negative matter", note="Already in main library."),
    Spec("JPP2014-AstrophysSpaceSci2.pdf", "Negative mass hypothesis in cosmology and the nature of dark energy", 2014, "galaxies", "duplicate-main", existing_ref="M13", kind="journal alt copy", useful_for="Same as M13", note="Alternate copy of M13 content."),
    Spec("JPP2014-ModPhysLettA.pdf", "Cosmological bimetric model with interacting positive and negative masses and two different speeds of light, in agreement with the observed acceleration of the Universe", 2014, "math_symmetry", "duplicate-main", existing_ref="M14", kind="journal", useful_for="Coupled metrics with two light speeds", note="Already in main library."),
    Spec("JPP2015-AstrophysSpaceSci.pdf", "Lagrangian derivation of the two coupled field equations in the Janus cosmological model", 2015, "bimetric_geodesics", "duplicate-main", existing_ref="M15", kind="journal", useful_for="Action-level derivation of coupled equations", note="Already in main library."),
    Spec("JPP2015-ModPhysLettA.pdf", "Cancellation of the central singularity of the Schwarzschild solution with natural mass inversion process", 2015, "compact_objects", "duplicate-main", existing_ref="M16", kind="journal", useful_for="Black-hole alternative genealogy", note="Already in main library."),
    Spec("JPP2016-Schwarzschild-virtual-singularity.pdf", "Schwarzschild 1916 seminal paper revisited : A virtual singularity", 2016, "compact_objects", "candidate-new", kind="preprint", useful_for="Critique of singularity reading; prehistory of plugstar branch", note="Useful in black-hole / bridge critique track."),
    Spec("JPP2017-janus-cosmological-model.pdf", "The Janus Cosmological Model. Fourty years of work", 2017, "bimetric_geodesics", "candidate-new", kind="long synthesis", useful_for="Historical synthesis of the full model", note="Good paper-native reference precursor, but not a single journal paper."),
    Spec("JPP2021-Janus-22-9.pdf", "Janus 22-9 companion document", 2021, "compact_objects", "supplement", kind="video annex", useful_for="Black-hole critique notes", note="Supplementary note, not a primary paper."),
    Spec("JPP2021-Janus-Cosmological-Model.pdf", "Bimetric models. When negative mass replaces both dark matter and dark energy. Excellent agreement with observational data. Solving the problem of the primeval antimatter", 2021, "bimetric_geodesics", "candidate-new", kind="preprint", useful_for="Core 2021 synthesis before 2024 EPJC paper", note="Important precursor for paper-native recreation."),
    Spec("JPP2021-Janus-Cosmological-Model-including-radiative-era-HAL.pdf", "Bimetric models ... Description of the radiative era", 2021, "expansion", "candidate-new", kind="HAL preprint", useful_for="Radiative era; early-universe branch", note="Directly useful for paper_plus_cited_comparison."),
    Spec("JPP2021-Nature-of-the-dipole-repeller.pdf", "Nature of the Dipole Repeller", 2021, "galaxies", "candidate-new", kind="preprint", useful_for="Large-scale structure / repeller interpretation", note="Observation-facing late-time structure paper."),
    Spec("JPP2022-janus22-5-5.pdf", "Janus 22 part 5 annex", 2022, "math_symmetry", "supplement", kind="video annex", useful_for="Equation-heavy annex to Janus 22 series", note="Supplementary note, not a primary paper."),
    Spec("JPP2022-Janus-22-9.pdf", "Janus 22-9 companion document", 2021, "compact_objects", "supplement", kind="video annex", useful_for="Black-hole critique notes", note="Same content family as the 2021 copy."),
    Spec("JPP2025-10-14-JMP-Alternative-to-Black-Holes-Gravastars-and-Plugstars.pdf", "Alternatives to Black Holes: Gravastars and Plugstars", 2025, "compact_objects", "duplicate-main", existing_ref="X2025-plugstars-jmp", kind="journal/preprint", useful_for="Plugstar branch", note="Already in main library."),
    Spec("JPP2026-01-JMP-Mathematical-and-Geometrical-Inconsistency-of-the-Black-Hole-Model.Part-I.pdf", "Mathematical and Geometrical Inconsistency of the Black Hole Model. Part I", 2026, "compact_objects", "duplicate-main", existing_ref="X2026-black-hole-inconsistency-I", kind="journal/preprint", useful_for="Black-hole inconsistency branch", note="Already in main library."),
    Spec("JPP2026-06-JMP-The-black-hole-model-goes-with-an-analytic-extension-of-spacetime.pdf", "The black hole model goes with an analytic extension of spacetime", 2026, "compact_objects", "duplicate-main", existing_ref="X2026-black-hole-analytic-extension", kind="journal/preprint", useful_for="Analytic extension critique", note="Already in main library."),
    Spec("JPP2026-07-07-Is-the-real-world-as-a-part-of-a-complex-reality.pdf", "Is the real world, as a part of complex reality?", 2026, "math_symmetry", "duplicate-main", existing_ref="X2026-complex-reality", kind="journal/preprint", useful_for="Complex Lorentz/Poincare and group structure", note="Already in main library."),
    Spec("LUT2020-janus-to-nature.pdf", "When negative mass replaces both dark matter and dark energy. Solving the problem of primordial antimatter", 2020, "bimetric_geodesics", "candidate-new", kind="submission/preprint", useful_for="Near-ancestor of the 2021 Janus synthesis", note="Useful to trace paper evolution."),
    Spec("Negativegravitationallensingeffect.pdf", "Negative gravitational lensing effect. Confinement by surrounding negative matter", 2014, "galaxies", "candidate-new", kind="preprint", useful_for="Negative lensing / confinement claims", note="Key galaxy/VLS support document."),
    Spec("solvingnegativemassparadox.pdf", "Solving the negative mass paradox", 2014, "bimetric_geodesics", "candidate-new", kind="preprint", useful_for="Runaway paradox resolution", note="Foundational and often cited informally."),
    Spec("Spiralstructure.pdf", "Bimetric theory: the only model which explains the nature of spiral structure ...", 2014, "galaxies", "candidate-new", kind="preprint", useful_for="Spiral/barred galaxy morphology", note="Directly useful for the galaxy branch."),
    Spec("The physical meaning of the A.Sakharov twin universe model .pdf", "The physical meaning of the A.Sakharov twin universe model", 2014, "math_symmetry", "candidate-new", kind="preprint", useful_for="Sakharov/twin-universe interpretation; antimatter geometry", note="Important bridge between Sakharov and later Janus formulations."),
    Spec("TheJanuscosmologicalmodelasananswertothecrisisincosmologyfr.pdf", "Le modele cosmologique Janus : une reponse a la crise profonde de la cosmologie d'aujourd'hui", 2021, "bimetric_geodesics", "candidate-new", kind="French synthesis", useful_for="French synthesis of crisis/Janus positioning", note="Useful as an exposition/synthesis source."),
    Spec("Very Large Structure numerical simulation in a compact computational space.pdf", "Very Large Structure numerical simulation in a compact computational space", 2014, "galaxies", "candidate-new", kind="preprint", useful_for="VLS simulation branch", note="Observation-facing structure formation document."),
]


KEYWORDS = {
    "negative mass",
    "dark energy",
    "dark matter",
    "antimatter",
    "spiral",
    "lens",
    "lensing",
    "repeller",
    "radiative",
    "acceleration",
    "cpt",
    "pt",
    "symplectic",
    "torsor",
    "wormhole",
    "black hole",
    "plugstar",
    "gravastar",
    "sakharov",
    "vls",
}


def extract_text(path: Path, max_pages: int = 2) -> tuple[int, str]:
    doc = fitz.open(path)
    page_count = len(doc)
    chunks = [doc[i].get_text("text") for i in range(min(max_pages, page_count))]
    text = " ".join(chunks)
    text = fix_text(text)
    text = text.replace("\x00", " ").replace("\uffff", " ")
    return page_count, " ".join(text.split()).strip()


def keyword_hits(text: str) -> list[str]:
    lower = text.lower()
    hits = [key for key in sorted(KEYWORDS) if key in lower]
    return hits


def compact(text: str, limit: int = 260) -> str:
    text = " ".join(text.split())
    return text[:limit] + ("..." if len(text) > limit else "")


def main() -> None:
    rows = []
    md_lines = [
        "# Janus Candidate Document Index",
        "",
        "Scope: candidate PDFs collected outside or alongside the main Janus library.",
        "",
        "Status meanings:",
        "- `duplicate-main`: already represented in `data/raw/janus_library/manifest.csv`.",
        "- `near-duplicate-main`: sub-series or precursor already broadly represented in main library.",
        "- `candidate-new`: useful document not yet canonically indexed in the main library.",
        "- `supplement`: annex / companion note, usually not a primary paper anchor.",
        "",
    ]

    for spec in SPECS:
        path = CANDIDATE_DIR / spec.file_name
        if not path.exists():
            continue
        page_count, text = extract_text(path)
        hits = ", ".join(keyword_hits(text))
        excerpt = compact(text)
        rows.append(
            {
                "file_name": spec.file_name,
                "title": spec.title,
                "year": spec.year,
                "axis": spec.axis,
                "status": spec.status,
                "existing_ref": spec.existing_ref,
                "kind": spec.kind,
                "pages": page_count,
                "useful_for": spec.useful_for,
                "keywords": hits,
                "note": spec.note,
            }
        )
        md_lines.extend(
            [
                f"## {spec.file_name}",
                "",
                f"- Title: {spec.title}",
                f"- Year: {spec.year}",
                f"- Axis: {spec.axis}",
                f"- Status: {spec.status}",
                f"- Existing ref: {spec.existing_ref or '-'}",
                f"- Kind: {spec.kind or '-'}",
                f"- Pages: {page_count}",
                f"- Useful for: {spec.useful_for or '-'}",
                f"- Keyword hits: {hits or '-'}",
                f"- Note: {spec.note or '-'}",
                f"- First-page cue: {excerpt}",
                "",
            ]
        )

    REPORT_CSV.parent.mkdir(parents=True, exist_ok=True)
    with REPORT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "file_name",
                "title",
                "year",
                "axis",
                "status",
                "existing_ref",
                "kind",
                "pages",
                "useful_for",
                "keywords",
                "note",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    REPORT_MD.write_text("\n".join(md_lines), encoding="utf-8")


if __name__ == "__main__":
    main()

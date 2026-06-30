from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from pypdf import PdfReader


REPORT_PATH = Path("outputs/reports/newtonian_source_anchor_verification.md")


@dataclass(frozen=True)
class Anchor:
    ref_id: str
    pdf_glob: str
    page: int
    phrase: str
    meaning: str


ANCHORS = [
    Anchor(
        ref_id="M15",
        pdf_glob="M15*.pdf",
        page=2,
        phrase="provides completely different interaction laws",
        meaning="M15 ties Eq. 5 density signs and Eq. 6 double Newtonian approximation to the Janus interaction laws.",
    ),
    Anchor(
        ref_id="M15",
        pdf_glob="M15*.pdf",
        page=6,
        phrase="Masses with same signs mutually attract",
        meaning="M15 restates same-sign attraction and opposite-sign repulsion as physical features.",
    ),
    Anchor(
        ref_id="M30",
        pdf_glob="M30*.pdf",
        page=17,
        phrase="Using the Newtonian approximation",
        meaning="M30 gives the mixed stationary equations and Newtonian tensor terms around Eqs. 105-106.",
    ),
    Anchor(
        ref_id="M30",
        pdf_glob="M30*.pdf",
        page=17,
        phrase="Masses of the same sign attract each other",
        meaning="M30 states the resulting interaction laws and runaway removal after Eq. 106.",
    ),
    Anchor(
        ref_id="M30",
        pdf_glob="M30*.pdf",
        page=20,
        phrase="4π",
        meaning="M30 TOV/Newtonian-limit section carries the standard gravitational normalization used by the weak-field convention.",
    ),
]


def pdf_for(anchor: Anchor) -> Path:
    matches = sorted(Path("data/raw/janus_library").glob(anchor.pdf_glob))
    if not matches:
        raise FileNotFoundError(f"Missing PDF for {anchor.ref_id}: {anchor.pdf_glob}")
    return matches[0]


def page_text(pdf_path: Path, page_number: int) -> str:
    reader = PdfReader(str(pdf_path))
    if page_number < 1 or page_number > len(reader.pages):
        raise ValueError(f"{pdf_path} has no page {page_number}")
    return " ".join((reader.pages[page_number - 1].extract_text() or "").split())


def snippet(text: str, phrase: str, window: int = 180) -> str:
    index = text.lower().find(phrase.lower())
    if index < 0:
        return ""
    return text[max(0, index - window) : index + len(phrase) + window]


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Newtonian Source Anchor Verification",
        "",
        "This verifies direct PDF anchors for the two-sector Newtonian-limit kernel.",
        "",
        "| ref | page | status | anchor phrase | meaning |",
        "|---|---:|---|---|---|",
    ]
    ok = True
    for anchor in ANCHORS:
        pdf_path = pdf_for(anchor)
        text = page_text(pdf_path, anchor.page)
        found = anchor.phrase.lower() in text.lower()
        ok = ok and found
        status = "ok" if found else "missing"
        display_phrase = anchor.phrase.replace("4π", "4*pi")
        lines.append(
            f"| {anchor.ref_id} | {anchor.page} | {status} | `{display_phrase}` | {anchor.meaning} |"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "The interaction signs are directly source-anchored. The compact Poisson RHS in code is a weak-field convention derived from those signs and standard Newtonian normalization; it is not quoted as a standalone equation in M15/M30.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

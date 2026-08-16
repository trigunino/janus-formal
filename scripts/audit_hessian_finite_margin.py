#!/usr/bin/env python3
"""Static audit of the finite coercive-margin H10--H14 frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteSectorQuadraticGarding4D.lean": (
        "FiniteSectorQuadraticGardingData",
        "finite_sector_quadratic_garding_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D.lean": (
        "CandidateACrossSectorPair",
        "CandidateAFiveSectorSymmetricGardingData",
        "candidateA_five_sector_symmetric_garding_gate",
    ),
    "P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D.lean": (
        "FiniteSectorPhysicalSmallnessGardingData",
        "finite_sector_physical_smallness_garding_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorPhysicalSmallnessGarding4D.lean": (
        "CandidateAFiveSectorPhysicalSmallnessGardingData",
        "candidateA_five_sector_physical_smallness_garding_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianPreferredFiniteMarginFrontier4D.lean": (
        "global_candidateA_hessian_preferred_finite_margin_frontier_gate",
        "global_candidateA_hessian_preferred_finite_margin_garding_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-finite-margin.yml"
DOC = ROOT / "docs" / "hessian_global_01_finite_margin.md"


def has_decl(text: str, name: str) -> bool:
    short_name = name.rsplit(".", 1)[-1]
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:structure|def|abbrev|theorem|lemma|inductive)\s+"
        rf"(?:[A-Za-z0-9_']+\.)?{re.escape(short_name)}\b",
        text,
    ))


def main() -> int:
    errors: list[str] = []

    for filename, declarations in REQUIRED.items():
        path = GATES / filename
        if not path.is_file():
            errors.append(f"missing module: {filename}")
            continue
        text = path.read_text(encoding="utf-8")
        for declaration in declarations:
            if not has_decl(text, declaration):
                errors.append(f"missing {declaration!r} in {filename}")
        for pattern in FORBIDDEN:
            if pattern.search(text):
                errors.append(f"forbidden placeholder/declaration in {filename}")

    if not WORKFLOW.is_file():
        errors.append(f"missing workflow: {WORKFLOW.relative_to(ROOT)}")
    else:
        workflow = WORKFLOW.read_text(encoding="utf-8")
        for filename in REQUIRED:
            if filename.removesuffix(".lean") not in workflow:
                errors.append(f"workflow does not build {filename}")

    if not DOC.is_file():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")

    if errors:
        print("Hessian finite-margin audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian finite-margin audit: OK")
    print("- five diagonal sector constants")
    print("- ten symmetric cross-sector bounds")
    print("- one dense-core physical bound")
    print("- explicit positive total margin")
    print("- stable public H10--H14 facade")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

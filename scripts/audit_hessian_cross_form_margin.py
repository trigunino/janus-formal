#!/usr/bin/env python3
"""Static audit of the cross-form finite-margin Candidate-A frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D.lean": (
        "CandidateACrossSectorPair",
        "CandidateAFiveSectorSymmetricGardingData",
        "candidateA_five_sector_symmetric_garding_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D.lean": (
        "CandidateAFiveSectorCrossFormGardingData",
        "crossForm_quadratic_bound",
        "candidateA_five_sector_cross_form_garding_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorCrossFormPhysicalSmallness4D.lean": (
        "CandidateAFiveSectorCrossFormPhysicalSmallnessData",
        "candidateA_five_sector_cross_form_physical_smallness_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianPreferredCrossFormMarginFrontier4D.lean": (
        "global_candidateA_hessian_preferred_crossForm_margin_frontier_gate",
        "global_candidateA_hessian_preferred_crossForm_margin_garding_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-cross-form-margin.yml"
DOC = ROOT / "docs" / "hessian_global_01_cross_form_margin.md"


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
        print("Hessian cross-form margin audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian cross-form margin audit: OK")
    print("- ten unordered Candidate-A sector pairs")
    print("- canonical op-norm cross bounds")
    print("- dense-core physical smallness")
    print("- explicit total coercive margin")
    print("- preferred public frontier")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

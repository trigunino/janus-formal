#!/usr/bin/env python3
"""Static audit of the preferred numerical action-symmetry H10--H14 route."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPGlobalCandidateASectorActionTranslationCanonicalSmallness4D.lean": (
        "GlobalCandidateASectorActionTranslationCanonicalSmallnessData4D",
        "global_candidateA_sector_action_translation_canonical_smallness_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationCanonicalSmallness4D.lean": (
        "GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D",
        "kernel_finrank_eq_profile_sum",
        "global_candidateA_profile_action_translation_canonical_smallness_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryExplicitSmallnessFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_sectorActionSymmetryExplicitSmallness_frontier_gate",
        "global_candidateA_hessian_canonicalSix_sectorActionSymmetryExplicitSmallness_exact_count",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryExplicitSmallnessFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_frontier_gate",
        "global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_exact_count",
    ),
    "P0EFTJanusProgramPGlobalHessianPreferredActionSymmetryFrontier4D.lean": (
        "global_candidateA_hessian_preferred_action_symmetry_frontier_gate",
        "global_candidateA_hessian_preferred_action_symmetry_exact_count",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-preferred-action-symmetry.yml"
DOC = ROOT / "docs" / "hessian_global_01_profile_explicit_smallness.md"


def has_decl(text: str, name: str) -> bool:
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:structure|def|abbrev|theorem|lemma)\s+"
        rf"(?:[A-Za-z0-9_']+\.)?{re.escape(name)}\b",
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
        print("Preferred action-symmetry Hessian audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Preferred action-symmetry Hessian audit: OK")
    print("- five D10-free numerical sector multiplicities")
    print("- exact action-translation zero modes")
    print("- explicit dense-core H11 smallness")
    print("- exact sector and profile kernel counts")
    print("- public preferred H10--H14 gate")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

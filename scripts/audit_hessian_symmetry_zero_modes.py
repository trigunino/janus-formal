#!/usr/bin/env python3
"""Static audit of the Candidate-A symmetry-generated zero-mode frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPSymmetryOrbitHessianKernel4D.lean": (
        "OrbitEventuallyInvariantAt",
        "fderiv_apply_eq_zero_of_orbitEventuallyInvariant",
        "secondFrechet_apply_eq_zero_of_gradientOrbitInvariant",
        "symmetry_orbit_hessian_kernel_gate",
    ),
    "P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D.lean": (
        "ActionTranslationEventuallyInvariantAt",
        "gradientOrbitInvariant_of_actionTranslationInvariant",
        "action_translation_symmetry_hessian_kernel_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAInfinitesimalSymmetryZeroModes4D.lean": (
        "GlobalCandidateAInfinitesimalSymmetryModes4D",
        "GlobalCandidateAInfinitesimalSymmetryModes4D.vector_annihilated",
        "GlobalCandidateAInfinitesimalSymmetryAutomaticSplit4D",
        "global_candidateA_infinitesimal_symmetry_zero_mode_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D.lean": (
        "GlobalCandidateAActionTranslationSymmetryModes4D",
        "GlobalCandidateAActionTranslationAutomaticSplit4D",
        "global_candidateA_action_translation_zero_mode_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActionSymmetrySectors4D.lean": (
        "GlobalCandidateAActionSymmetrySectorData4D",
        "GlobalCandidateAActionSymmetrySectorData4D.kernel_finrank_eq_sum",
        "global_candidateA_action_symmetry_sector_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSymmetryOrbitFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_symmetryOrbit_frontier_gate",
        "global_candidateA_hessian_canonicalSix_symmetryOrbit_exact_kernel",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_actionSymmetry_frontier_gate",
        "global_candidateA_hessian_canonicalSix_actionSymmetry_exact_count",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-symmetry-zero-modes.yml"
DOC = ROOT / "docs" / "hessian_global_01_symmetry_zero_modes.md"


def has_decl(text: str, name: str) -> bool:
    short_name = name.rsplit(".", 1)[-1]
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:structure|def|abbrev|theorem|lemma)\s+"
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
        print("Hessian symmetry-zero-mode audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian symmetry-zero-mode audit: OK")
    print("- action invariance -> gradient invariance")
    print("- gradient invariance -> second Frechet kernel")
    print("- Candidate-A Riesz annihilation")
    print("- automatic splitting and no-hidden-mode Garding")
    print("- canonical-six H10-H14 terminal facade")
    print("- D10-free physical sector count")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

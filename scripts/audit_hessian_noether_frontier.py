#!/usr/bin/env python3
"""Static audit of the Candidate-A Noether/action-symmetry Hessian frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPNoetherHessianKernel4D.lean": (
        "NoetherModeGermAt",
        "noetherMode_hessian_right_zero",
        "noetherMode_riesz_zero",
        "noether_hessian_kernel_gate",
    ),
    "P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D.lean": (
        "ActionTranslationEventuallyInvariantAt",
        "gradientOrbitInvariant_of_actionTranslationInvariant",
        "action_translation_symmetry_hessian_kernel_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualNoetherModes4D.lean": (
        "GlobalCandidateAActualNoetherModeAt",
        "GlobalCandidateAActualNoetherModeFamily4D",
        "globalCandidateAActualNoetherMode_operator_zero",
        "global_candidateA_actual_noether_modes_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D.lean": (
        "GlobalCandidateAActionTranslationSymmetryModes4D",
        "GlobalCandidateAActionTranslationAutomaticSplit4D",
        "global_candidateA_action_translation_zero_mode_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualNoetherGarding4D.lean": (
        "GlobalCandidateAActualNoetherGardingData4D",
        "GlobalCandidateAActualNoetherGardingData4D.toAutomaticSplit",
        "global_candidateA_actual_noether_garding_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualNoetherOrthogonalGarding4D.lean": (
        "GlobalCandidateAActualNoetherOrthogonalGardingData4D",
        "GlobalCandidateAActualNoetherOrthogonalGardingData4D.toOrthogonalGarding",
        "global_candidateA_actual_noether_orthogonal_garding_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualNoetherStablePhysicalForm4D.lean": (
        "GlobalCandidateAActualNoetherStablePhysicalFormData4D",
        "GlobalCandidateAActualNoetherStablePhysicalFormData4D.physical_operator_small",
        "GlobalCandidateAActualNoetherStablePhysicalFormData4D.toOrthogonalGarding",
        "global_candidateA_actual_noether_stable_physical_form_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D.lean": (
        "GlobalCandidateAActionTranslationStablePhysicalFormData4D",
        "GlobalCandidateAActionTranslationStablePhysicalFormData4D.physical_operator_small",
        "GlobalCandidateAActionTranslationStablePhysicalFormData4D.toOrthogonalGarding",
        "global_candidateA_action_translation_stable_physical_form_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixNoetherFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_noether_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixNoetherOrthogonalFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_noetherOrthogonal_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixNoetherStableFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_noetherStable_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryStableFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_actionSymmetryStable_frontier_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-noether-frontier.yml"
DOC = ROOT / "docs" / "hessian_global_01_noether_frontier.md"


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
        print("Hessian Noether frontier audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian Noether frontier audit: OK")
    print("- germ-level Noether identity implies Hessian kernel")
    print("- exact action translation symmetry implies Noether identity")
    print("- actual Candidate-A Riesz operator annihilation")
    print("- automatic finite-span splitting and no-hidden-mode closure")
    print("- orthogonality-derived independence")
    print("- principal Garding plus small H11 form")
    print("- terminal canonical-six action-symmetry frontier")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

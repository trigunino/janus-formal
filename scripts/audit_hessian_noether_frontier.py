#!/usr/bin/env python3
"""Static audit of the Candidate-A action-symmetry Hessian frontier."""

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
    "P0EFTJanusProgramPDenseBilinearOpNorm4D.lean": (
        "continuousBilinear_opNorm_le_of_dense",
        "dense_bilinear_opNorm_gate",
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
    "P0EFTJanusProgramPGlobalCandidateASevenPhysicalExtensionNorm4D.lean": (
        "globalCandidateASevenPhysicalExtension_form_opNorm_le",
        "global_candidateA_seven_physical_extension_norm_gate",
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
    "P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D.lean": (
        "globalCandidateACanonicalSevenPhysicalConstant",
        "globalCandidateACanonicalSixPhysicalExtension_form_opNorm_le",
        "GlobalCandidateAActionTranslationCanonicalSmallnessData4D",
        "global_candidateA_canonical_physical_smallness_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASectorActionTranslationCanonicalSmallness4D.lean": (
        "GlobalCandidateASectorActionTranslationCanonicalSmallnessData4D",
        "GlobalCandidateASectorActionTranslationCanonicalSmallnessData4D.toGlobal",
        "GlobalCandidateASectorActionTranslationCanonicalSmallnessData4D.kernel_finrank_eq_sector_sum",
        "global_candidateA_sector_action_translation_canonical_smallness_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationCanonicalSmallness4D.lean": (
        "GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D",
        "GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D.kernel_finrank_eq_profile_sum",
        "global_candidateA_profile_action_translation_canonical_smallness_gate",
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
    "P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryExplicitSmallnessFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_actionSymmetryExplicitSmallness_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryExplicitSmallnessFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_sectorActionSymmetryExplicitSmallness_frontier_gate",
        "global_candidateA_hessian_canonicalSix_sectorActionSymmetryExplicitSmallness_exact_count",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryExplicitSmallnessFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_frontier_gate",
        "global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_exact_count",
    ),
}

PREFERRED_WORKFLOW_ONLY = {
    "P0EFTJanusProgramPGlobalCandidateASectorActionTranslationCanonicalSmallness4D.lean",
    "P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationCanonicalSmallness4D.lean",
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryExplicitSmallnessFrontier4D.lean",
    "P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryExplicitSmallnessFrontier4D.lean",
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
        for filename in REQUIRED.keys() - PREFERRED_WORKFLOW_ONLY:
            if filename.removesuffix(".lean") not in workflow:
                errors.append(f"workflow does not build {filename}")

    if not DOC.is_file():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")

    if errors:
        print("Hessian action-symmetry frontier audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian action-symmetry frontier audit: OK")
    print("- action invariance implies the actual Hessian kernel equation")
    print("- orthogonality supplies linear independence")
    print("- Garding excludes hidden zero modes")
    print("- dense-core constants bound the completed H11 form")
    print("- principal Garding plus explicit H11 smallness")
    print("- five D10-free sector multiplicities")
    print("- numerical-profile exact kernel count")
    print("- terminal H10--H14 action-symmetry frontiers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Static audit of the five-sector Candidate-A zero-mode frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPCandidateASectorModeAssembly4D.lean": (
        "CandidateASectorModeTypes",
        "CandidateASectorOrthogonalModeFamily",
        "CandidateASectorOrthogonalModeFamily.global_orthogonal",
        "candidateA_sector_mode_assembly_gate",
    ),
    "P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D.lean": (
        "CandidateASectorOrthogonalSubspaces",
        "CandidateASectorSubspaceModeFamily",
        "CandidateASectorSubspaceModeFamily.toOrthogonalModeFamily",
        "candidateA_sector_subspace_mode_gate",
    ),
    "P0EFTJanusProgramPCandidateASectorModeMultiplicity4D.lean": (
        "candidateASectorClassificationFiberEquiv",
        "candidateASectorMultiplicity_eq_card",
        "candidateASectorGlobalMode_card",
    ),
    "P0EFTJanusProgramPCandidateASectorMultiplicityProfile4D.lean": (
        "CandidateASectorMultiplicityProfile",
        "CandidateASectorMultiplicityProfile.modeTypes",
        "CandidateASectorMultiplicityProfile.globalMode_card",
    ),
    "P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D.lean": (
        "GlobalCandidateASectorActionTranslationStablePhysicalFormData4D",
        "GlobalCandidateASectorActionTranslationStablePhysicalFormData4D.toStable",
        "global_candidateA_sector_action_translation_stable_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASectorSubspaceActionTranslationStablePhysicalForm4D.lean": (
        "GlobalCandidateASectorSubspaceActionTranslationStablePhysicalFormData4D",
        "GlobalCandidateASectorSubspaceActionTranslationStablePhysicalFormData4D.toSectorStable",
        "global_candidateA_sector_subspace_action_translation_stable_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASectorStableMultiplicity4D.lean": (
        "GlobalCandidateASectorActionTranslationStablePhysicalFormData4D.kernel_finrank_eq_explicit_sector_cards",
        "global_candidateA_sector_stable_explicit_multiplicity_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationStablePhysicalForm4D.lean": (
        "GlobalCandidateAProfileActionTranslationStablePhysicalFormData4D",
        "GlobalCandidateAProfileActionTranslationStablePhysicalFormData4D.kernel_finrank_eq_profile_sum",
        "global_candidateA_profile_action_translation_stable_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryStableFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_sectorActionSymmetryStable_frontier_gate",
        "global_candidateA_hessian_canonicalSix_sectorActionSymmetryStable_exact_count",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSectorSubspaceActionSymmetryStableFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_sectorSubspaceActionSymmetryStable_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryStableFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_profileActionSymmetryStable_frontier_gate",
        "global_candidateA_hessian_canonicalSix_profileActionSymmetryStable_exact_count",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-sector-modes.yml"
DOC = ROOT / "docs" / "hessian_global_01_sector_mode_profile.md"


def has_decl(text: str, name: str) -> bool:
    short_name = name.rsplit(".", 1)[-1]
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:structure|def|abbrev|theorem|lemma|instance)\s+"
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
        print("Hessian sector-mode audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian sector-mode audit: OK")
    print("- dependent sum of five D10-free mode sectors")
    print("- orthogonal physical subspaces and inherited cross pairings")
    print("- global nonzero and orthogonality assembly")
    print("- exact classification-fiber cardinalities")
    print("- numerical five-sector multiplicity profile")
    print("- stable action-symmetry Candidate-A adapters")
    print("- terminal H10-H14 sector-counting facades")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

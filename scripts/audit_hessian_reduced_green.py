#!/usr/bin/env python3
"""Static audit of the reduced Candidate-A Hessian, Green and resolvent chain."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteDefectKernelIdentification4D.lean": (
        "finiteDefect_operator_ker_eq_projection_range",
    ),
    "P0EFTJanusProgramPFiniteDefectRangeIdentification4D.lean": (
        "finiteDefect_operator_range_eq_projection_ker",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedOperator4D.lean": (
        "finiteDefectReducedOperator",
        "finiteDefectReducedOperator_injective",
        "finiteDefectReducedOperator_surjective",
        "finite_defect_reduced_operator_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedInverse4D.lean": (
        "finiteDefectReducedEquiv",
        "finiteDefectReducedInverse",
        "finiteDefectReducedInverse_opNorm_le",
        "finite_defect_reduced_inverse_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedResolvent4D.lean": (
        "finiteDefectReducedOperator_isSelfAdjoint",
        "finiteDefectReducedShiftedOperator",
        "finiteDefectReducedRealResolvent",
        "finiteDefectReducedRealResolvent_opNorm_le",
        "finite_defect_reduced_real_resolvent_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedResolventIdentity4D.lean": (
        "finiteDefectReducedRealResolvent_identity",
        "finiteDefectReducedRealResolvent_sub_opNorm_le",
        "finite_defect_reduced_real_resolvent_identity_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedOperator4D.lean": (
        "globalCandidateAAugmentedReducedOperator",
        "global_candidateA_augmented_reduced_operator_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedInverse4D.lean": (
        "globalCandidateAAugmentedReducedInverse",
        "global_candidateA_augmented_reduced_inverse_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolvent4D.lean": (
        "globalCandidateAAugmentedReducedRealResolvent",
        "global_candidateA_augmented_reduced_resolvent_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolventIdentity4D.lean": (
        "globalCandidateAAugmentedReducedRealResolvent_identity",
        "globalCandidateAAugmentedReducedRealResolvent_sub_opNorm_le",
        "global_candidateA_augmented_reduced_resolvent_identity_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianReducedGreenCertificate4D.lean": (
        "GlobalCandidateAHessianReducedGreenCertificate4D",
        "global_candidateA_hessian_reducedGreen_certificate_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianReducedGreenFrontier4D.lean": (
        "global_candidateA_hessian_reducedGreen_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianReducedResolventCertificate4D.lean": (
        "globalCandidateAHessianReducedResolventInterval",
        "GlobalCandidateAHessianReducedResolventCertificate4D",
        "global_candidateA_hessian_reducedResolvent_certificate_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianReducedResolventFrontier4D.lean": (
        "global_candidateA_hessian_reducedResolvent_frontier_gate",
    ),
    "P0EFTJanusProgramPSelfAdjointSmallPerturbation4D.lean": (
        "SelfAdjointSmallPerturbationData",
        "selfAdjointSmallPerturbation_lowerBound",
        "self_adjoint_small_perturbation_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-reduced-green.yml"


def has_decl(text: str, name: str) -> bool:
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:noncomputable\s+)?(?:structure|def|abbrev|theorem|lemma)\s+{re.escape(name)}\b",
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
            stem = filename.removesuffix(".lean")
            if stem not in workflow:
                errors.append(f"workflow does not build {stem}")

    if errors:
        print("Reduced Hessian/Green/resolvent audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Reduced Hessian/Green/resolvent audit: OK")
    print("- exact zero modes and range complement")
    print("- bijective reduced Hessian")
    print("- continuous reduced Green operator")
    print("- explicit inverse norm bound")
    print("- open real resolvent interval")
    print("- first resolvent identity")
    print("- quantitative operator-norm continuity")
    print("- small self-adjoint perturbation gap")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

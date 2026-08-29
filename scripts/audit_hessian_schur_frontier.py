#!/usr/bin/env python3
"""Static audit of the finite-mode Schur H10--H14 frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteModeSchurKernel4D.lean": (
        "FiniteModeSchurKernelData",
        "finiteModeSchurKernelEquiv",
        "finiteModeSchurKernelModel",
        "finite_mode_schur_kernel_gate",
    ),
    "P0EFTJanusProgramPFiniteModeSchurBlockElimination4D.lean": (
        "FiniteModeSchurBlockData",
        "finiteModeSchurBlockOperator",
        "finiteModeSchurBlock_factorization",
        "finite_mode_schur_block_elimination_gate",
    ),
    "P0EFTJanusProgramPFiniteModeSchurClosedRange4D.lean": (
        "FiniteModeSchurClosedRangeData",
        "finiteModeSchur_operatorRange_eq_preimage",
        "finiteModeSchur_operatorRange_closed",
        "finite_mode_schur_closed_range_gate",
    ),
    "P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D.lean": (
        "FiniteModeContinuousSchurBlockData",
        "finiteModeContinuousSchurRangeCoordinates",
        "finiteModeContinuousSchur_operatorRange_closed",
        "finite_mode_continuous_schur_block_gate",
    ),
    "P0EFTJanusProgramPFiniteModeSchurNondegenerate4D.lean": (
        "FiniteModeSchurNondegenerateData",
        "finiteModeSchur_operator_bijective",
        "finiteModeSchurFullGreen",
        "finite_mode_schur_nondegenerate_gate",
    ),
    "P0EFTJanusProgramPFiniteModeSchurDeterminant4D.lean": (
        "FiniteModeSchurDeterminantData",
        "finiteModeSchurMatrix",
        "finiteModeSchurBlockOperator_bijective_of_det_ne_zero",
        "finite_mode_schur_determinant_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualSchurZeroMode4D.lean": (
        "GlobalCandidateAActualSchurZeroModeData4D",
        "GlobalCandidateAActualSchurZeroModeData4D.toActualZeroModeGap",
        "global_candidateA_actual_schur_zeroMode_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualSchurClosedRange4D.lean": (
        "GlobalCandidateAActualSchurClosedRangeData4D",
        "global_candidateA_actual_schur_closedRange_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualContinuousSchurBlock4D.lean": (
        "GlobalCandidateAActualContinuousSchurBlockData4D",
        "global_candidateA_actual_continuous_schur_block_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D.lean": (
        "GlobalCandidateAActualBoundedSchurBlockData4D",
        "global_candidateA_actual_bounded_schur_block_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualSchurNondegenerate4D.lean": (
        "GlobalCandidateAActualBoundedSchurNondegenerateData4D",
        "globalCandidateAActualFullGreen",
        "global_candidateA_actual_schur_nondegenerate_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D.lean": (
        "GlobalCandidateAActualSchurDeterminantData4D",
        "global_candidateA_actual_schur_determinant_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianSchurZeroModeFrontier4D.lean": (
        "global_candidateA_hessian_schur_zeroMode_frontier_gate",
        "global_candidateA_hessian_schur_zeroMode_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianContinuousSchurFrontier4D.lean": (
        "global_candidateA_hessian_continuous_schur_frontier_gate",
        "global_candidateA_hessian_continuous_schur_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianBoundedSchurFrontier4D.lean": (
        "global_candidateA_hessian_bounded_schur_frontier_gate",
        "global_candidateA_hessian_bounded_schur_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianNondegenerateSchurFrontier4D.lean": (
        "global_candidateA_hessian_nondegenerate_schur_frontier_gate",
        "global_candidateA_hessian_nondegenerate_zero_modes",
    ),
    "P0EFTJanusProgramPGlobalHessianSchurDeterminantFrontier4D.lean": (
        "global_candidateA_hessian_schur_determinant_frontier_gate",
        "globalCandidateAHessianFiniteSchurDeterminant",
        "globalCandidateAHessianFiniteSchurDeterminant_ne_zero",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-schur-frontier.yml"
DOC = ROOT / "docs" / "hessian_global_01_schur_frontier.md"


def has_decl(text: str, name: str) -> bool:
    short_name = name.rsplit(".", 1)[-1]
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:noncomputable\s+)?(?:structure|def|abbrev|theorem|lemma)\s+"
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
        print("Hessian Schur frontier audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian Schur frontier audit: OK")
    print("- finite Schur kernel equivalence")
    print("- algebraic and bounded four-block Gaussian elimination")
    print("- closed range from automatically constructed coordinates")
    print("- finite determinant nondegeneracy criterion")
    print("- full Candidate-A Green on the zero-mode-free stratum")
    print("- terminal H10--H14 Green/resolvent/stability façades")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

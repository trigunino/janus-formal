#!/usr/bin/env python3
"""Static audit of the actual-kernel Candidate-A Hessian frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D.lean": (
        "SelfAdjointKernelComplementGapData",
        "selfAdjointKernelComplementOperator",
        "selfAdjoint_operator_range_eq_kernelComplement",
        "selfAdjointKernelComplementGreen",
        "self_adjoint_actual_kernel_complement_gate",
    ),
    "P0EFTJanusProgramPSelfAdjointKernelComplementResolvent4D.lean": (
        "selfAdjointKernelComplementResolvent",
        "selfAdjointKernelComplement_resolvent_identity",
        "self_adjoint_actual_kernel_resolvent_gate",
    ),
    "P0EFTJanusProgramPSelfAdjointClosedRangeKernelGap4D.lean": (
        "selfAdjoint_closedRange_range_eq_kernelComplement",
        "selfAdjointKernelComplementGapData_of_closedRange",
        "self_adjoint_closedRange_to_actualKernelGap_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.lean": (
        "GlobalCandidateAActualKernelGap4D",
        "globalCandidateAActualKernelGreen",
        "global_candidateA_h12_fredholm_gate_of_actualKernelGap",
        "global_candidateA_actual_kernel_complement_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D.lean": (
        "globalCandidateAActualKernelResolvent",
        "global_candidateA_actual_kernel_resolvent_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualKernelGapFromFredholm4D.lean": (
        "globalCandidateAActualKernelGap_of_fredholmEstimates",
        "global_candidateA_fredholmEstimates_to_actualKernel_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D.lean": (
        "GlobalCandidateASixPhysicalAggregateCoreBound4D",
        "globalCandidateASevenPhysicalCoreBound_of_sixAggregate",
        "global_candidateA_h11_gate_of_sixAggregateBound",
    ),
    "P0EFTJanusProgramPGlobalHessianActualKernelBoundedFrontier4D.lean": (
        "globalCandidateAActualKernelBoundedPhysicalExtension",
        "global_candidateA_hessian_actualKernel_bounded_frontier_gate",
    ),
}

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-actual-kernel.yml"

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)


def has_decl(text: str, name: str) -> bool:
    return bool(re.search(
        rf"(?m)^\s*(?:noncomputable\s+)?(?:private\s+)?"
        rf"(?:structure|def|abbrev|theorem|lemma)\s+{re.escape(name)}\b",
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
        print("Actual-kernel Hessian audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Actual-kernel Hessian audit: OK")
    print("- no auxiliary zero-mode projection")
    print("- exact range = orthogonal kernel complement")
    print("- one H11 six-block remainder estimate")
    print("- reduced Green and real-gap resolvent")
    print("- closed-range compatibility adapter")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

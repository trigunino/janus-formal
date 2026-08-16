#!/usr/bin/env python3
"""Static audit of the classified-zero-mode Hessian frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteKernelModel4D.lean": (
        "FiniteKernelModel",
        "kernel_finrank_eq_card",
        "SelfAdjointKernelComplementGapWithModel",
        "finite_kernel_model_actual_gap_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualZeroModeModel4D.lean": (
        "GlobalCandidateAActualZeroModeGap4D",
        "global_candidateA_actual_zeroMode_model_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D.lean": (
        "GlobalCandidateACommonHilbertToLocalChart4D",
        "globalCandidateASixPhysicalAggregateExtension_of_chartPullback",
        "global_candidateA_h11_gate_of_chartPullback",
    ),
    "P0EFTJanusProgramPSelfAdjointKernelComplementStability4D.lean": (
        "SelfAdjointKernelComplementPerturbationData",
        "selfAdjointKernelComplementPerturbedGreen",
        "self_adjoint_actual_kernel_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D.lean": (
        "GlobalCandidateAActualKernelPerturbation4D",
        "global_candidateA_actual_kernel_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D.lean": (
        "global_candidateA_hessian_actualKernel_chart_frontier_gate",
        "global_candidateA_hessian_actualKernel_chart_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D.lean": (
        "global_candidateA_hessian_zeroModeModel_frontier_gate",
        "global_candidateA_hessian_zeroModeModel_stability_gate",
    ),
}

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-zero-mode-model.yml"

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
        print("Zero-mode-model Hessian audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Zero-mode-model Hessian audit: OK")
    print("- explicit finite zero-mode coordinates")
    print("- exact kernel dimension")
    print("- bounded common-to-chart realization")
    print("- H11 pullback from genuine local Hessians")
    print("- actual-kernel Green, resolvent and stability")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

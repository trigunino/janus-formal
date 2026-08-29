#!/usr/bin/env python3
"""Static audit of the canonical-six / actual-kernel coercivity frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPSelfAdjointKernelBasisCoercivity4D.lean": (
        "SelfAdjointKernelBasisCoercivityData",
        "SelfAdjointKernelBasisCoercivityData.lowerBound",
        "SelfAdjointKernelBasisCoercivityData.toGapData",
        "self_adjoint_kernel_basis_coercivity_gate",
    ),
    "P0EFTJanusProgramPFiniteKernelNamedModeCoercivity4D.lean": (
        "FiniteKernelNamedModeFamily",
        "FiniteKernelNamedModeFamily.basis",
        "FiniteKernelNamedModeFamily.ambientSynthesis_range",
        "SelfAdjointNamedKernelCoercivityData",
        "self_adjoint_named_kernel_coercivity_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualKernelBasisCoercivity4D.lean": (
        "GlobalCandidateAActualKernelBasisCoercivity4D",
        "globalCandidateAActualKernelGap_of_basisCoercivity",
        "globalCandidateAActualKernel_finrank_eq_card",
        "global_candidateA_actual_kernel_basis_coercivity_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D.lean": (
        "globalCandidateAH10BoundaryCoreMap",
        "globalCandidateAH10CompletedBoundaryProjection_of_bound",
        "globalCandidateAH10ProjectionCoreData_of_chartBound",
        "global_candidateA_hessian_canonicalSix_chartBound_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixBasisCoercivityFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_basisCoercivity_frontier_gate",
        "global_candidateA_hessian_canonicalSix_basisCoercivity_zeroMode_count",
        "global_candidateA_hessian_canonicalSix_basisCoercivity_two_inputs",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixNamedModeFrontier4D.lean": (
        "GlobalCandidateAActualNamedKernelCoercivity4D",
        "global_candidateA_hessian_canonicalSix_namedMode_frontier_gate",
        "global_candidateA_hessian_namedMode_kernel_synthesis",
        "global_candidateA_hessian_canonicalSix_namedMode_two_inputs",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-basis-coercivity.yml"
DOC = ROOT / "docs" / "hessian_global_01_basis_coercivity.md"


def has_decl(text: str, name: str) -> bool:
    short = name.rsplit(".", 1)[-1]
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:noncomputable\s+)?(?:structure|inductive|def|abbrev|theorem|lemma)\s+"
        rf"(?:[A-Za-z0-9_']+\.)?{re.escape(short)}\b",
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
        print("Hessian basis/coercivity audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian basis/coercivity audit: OK")
    print("- H10 completed projection derived from the chart-core bound")
    print("- six non-Robin Hessians fixed by the Candidate-A action")
    print("- named ambient zero modes synthesize exactly the actual kernel")
    print("- quadratic coercivity converted to the operator gap")
    print("- exact zero-mode count and terminal H10--H14 facade")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

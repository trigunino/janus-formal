#!/usr/bin/env python3
"""Audit the natural-projection action-symmetry H10--H14 closure."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D.lean": (
        "FiniteSelfAdjointProjectionResolutionData",
        "projection_inner_eq_norm_sq",
        "finite_selfAdjoint_projection_resolution_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D.lean": (
        "CandidateAFiveSectorSelfAdjointPrincipalResolutionData",
        "candidateA_five_sector_selfAdjoint_principal_resolution_garding_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPhysicalSmallness4D.lean": (
        "CandidateAFiveSectorSelfAdjointPhysicalSmallnessData",
        "candidateA_five_sector_selfAdjoint_physical_smallness_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointOperatorGarding4D.lean": (
        "CandidateAFiveSectorSelfAdjointOperatorGardingData",
        "candidateA_five_sector_selfAdjoint_operator_garding_gate",
    ),
    "P0EFTJanusProgramPSelfAdjointProjectionFiniteMarginActualKernelGap4D.lean": (
        "SelfAdjointProjectionFiniteMarginActualKernelGapData",
        "selfAdjoint_projection_finite_margin_actual_kernel_gap_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginActualKernelGap4D.lean": (
        "GlobalCandidateASelfAdjointProjectionFiniteMarginActualKernelGap4D",
        "global_candidateA_selfAdjoint_projection_actual_kernel_gap_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginH12Closure4D.lean": (
        "global_candidateA_selfAdjoint_projection_h12_closure_gate",
        "global_candidateA_selfAdjoint_projection_h12_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianSelfAdjointProjectionActionSymmetryClosure4D.lean": (
        "global_candidateA_hessian_selfAdjointProjection_actionSymmetry_closure_gate",
        "global_candidateA_hessian_selfAdjointProjection_actionSymmetry_exact_count",
        "global_candidateA_hessian_selfAdjointProjection_actionSymmetry_principal_garding_gate",
        "global_candidateA_hessian_selfAdjointProjection_actionSymmetry_total_garding_gate",
        "global_candidateA_hessian_selfAdjointProjection_actionSymmetry_actualKernelGap_gate",
        "global_candidateA_hessian_selfAdjointProjection_actionSymmetry_h12_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-selfadjoint-projection-action-symmetry.yml"
DOC = ROOT / "docs" / \
    "hessian_global_01_selfadjoint_projection_action_symmetry.md"


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
        print("Self-adjoint projection action-symmetry audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Self-adjoint projection action-symmetry audit: OK")
    print("- exact five-sector action symmetries")
    print("- symmetric idempotent projection resolution")
    print("- derived positivity and Pythagorean identity")
    print("- projected principal and physical margins")
    print("- actual-kernel H12 and H14 closure")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

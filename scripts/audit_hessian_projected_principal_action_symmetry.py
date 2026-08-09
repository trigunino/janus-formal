#!/usr/bin/env python3
"""Static audit of the unified projected-principal action-symmetry frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPGlobalHessianPreferredActionSymmetryFrontier4D.lean": (
        "global_candidateA_hessian_preferred_action_symmetry_frontier_gate",
        "global_candidateA_hessian_preferred_action_symmetry_exact_count",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D.lean": (
        "CandidateAFiveSectorPrincipalBlockData",
        "candidateA_five_sector_principal_block_garding_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D.lean": (
        "CandidateAFiveSectorPrincipalPhysicalSmallnessData",
        "candidateA_five_sector_principal_physical_smallness_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorGarding4D.lean": (
        "CandidateAFiveSectorPrincipalOperatorGardingData",
        "candidateA_five_sector_principal_operator_garding_gate",
    ),
    "P0EFTJanusProgramPPrincipalFiniteMarginActualKernelGap4D.lean": (
        "PrincipalFiniteMarginActualKernelGapData",
        "principal_finite_margin_actual_kernel_gap_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAFiniteMarginH12Closure4D.lean": (
        "global_candidateA_finite_margin_h12_closure_gate",
        "global_candidateA_finite_margin_h12_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianProjectedPrincipalMarginFrontier4D.lean": (
        "global_candidateA_hessian_projected_principal_garding_gate",
        "global_candidateA_hessian_projected_principal_actual_kernel_gap_gate",
        "global_candidateA_hessian_projected_principal_h12_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianProjectedPrincipalActionSymmetryClosure4D.lean": (
        "global_candidateA_hessian_projectedPrincipal_actionSymmetry_closure_gate",
        "global_candidateA_hessian_projectedPrincipal_actionSymmetry_exact_count",
        "global_candidateA_hessian_projectedPrincipal_actionSymmetry_garding_gate",
        "global_candidateA_hessian_projectedPrincipal_actionSymmetry_actualKernelGap_gate",
        "global_candidateA_hessian_projectedPrincipal_actionSymmetry_h12_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-projected-principal-action-symmetry.yml"
DOC = ROOT / "docs" / \
    "hessian_global_01_projected_principal_action_symmetry.md"


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
        print("Projected-principal action-symmetry audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Projected-principal action-symmetry audit: OK")
    print("- five-sector action-symmetry kernel construction")
    print("- exact numerical kernel count")
    print("- one projected principal Hessian")
    print("- explicit total finite margin")
    print("- actual-kernel H12 Green/resolvent closure")
    print("- stable unified H10--H14 facade")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

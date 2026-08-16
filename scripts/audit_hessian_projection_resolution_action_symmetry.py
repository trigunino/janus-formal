#!/usr/bin/env python3
"""Audit the positive-projection action-symmetry H10--H14 closure."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteProjectionNormResolution4D.lean": (
        "FiniteProjectionNormResolutionData",
        "norm_sq_decomposition",
        "finite_projection_norm_resolution_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D.lean": (
        "CandidateAFiveSectorPrincipalProjectionResolutionData",
        "candidateA_five_sector_projection_resolution_garding_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorProjectionPhysicalSmallness4D.lean": (
        "CandidateAFiveSectorProjectionPhysicalSmallnessData",
        "candidateA_five_sector_projection_physical_smallness_gate",
    ),
    "P0EFTJanusProgramPCandidateAFiveSectorProjectionOperatorGarding4D.lean": (
        "CandidateAFiveSectorProjectionOperatorGardingData",
        "candidateA_five_sector_projection_operator_garding_gate",
    ),
    "P0EFTJanusProgramPProjectionFiniteMarginActualKernelGap4D.lean": (
        "ProjectionFiniteMarginActualKernelGapData",
        "projection_finite_margin_actual_kernel_gap_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAProjectionFiniteMarginActualKernelGap4D.lean": (
        "GlobalCandidateAProjectionFiniteMarginActualKernelGap4D",
        "global_candidateA_projection_finite_margin_actual_kernel_gap_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAProjectionFiniteMarginH12Closure4D.lean": (
        "global_candidateA_projection_finite_margin_h12_closure_gate",
        "global_candidateA_projection_finite_margin_h12_stability_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianProjectionResolutionActionSymmetryClosure4D.lean": (
        "global_candidateA_hessian_projectionResolution_actionSymmetry_closure_gate",
        "global_candidateA_hessian_projectionResolution_actionSymmetry_exact_count",
        "global_candidateA_hessian_projectionResolution_actionSymmetry_garding_gate",
        "global_candidateA_hessian_projectionResolution_actionSymmetry_actualKernelGap_gate",
        "global_candidateA_hessian_projectionResolution_actionSymmetry_h12_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-projection-resolution-action-symmetry.yml"
DOC = ROOT / "docs" / \
    "hessian_global_01_projection_resolution_action_symmetry.md"


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
        print("Projection-resolution action-symmetry audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Projection-resolution action-symmetry audit: OK")
    print("- five-sector exact action symmetries")
    print("- positive resolution of the identity")
    print("- derived Pythagorean norm decomposition")
    print("- projected principal finite margin")
    print("- Candidate-A actual-kernel H12 closure")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Static audit of the reduced Hessian zeta/Quillen chain."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPIntrinsicNuclearTrace4D.lean": (
        "IntrinsicNuclearTraceData",
        "intrinsicNuclearTrace",
        "intrinsic_nuclear_trace_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedIntrinsicRelativeTrace4D.lean": (
        "FiniteDefectReducedIntrinsicRelativeTraceData",
        "finiteDefectReducedIntrinsicRelativeHeatTrace",
        "finite_defect_reduced_intrinsic_relative_trace_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedIntrinsicRelativeTrace4D.lean": (
        "GlobalCandidateAAugmentedReducedIntrinsicRelativeTraceData4D",
        "globalCandidateAAugmentedReducedIntrinsicRelativeHeatTrace",
    ),
    "P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.lean": (
        "RelativeHeatFinitePartData",
        "relativeHeatFinitePartDeterminant",
        "relative_heat_finite_part_determinant_gate",
    ),
    "P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D.lean": (
        "RelativeHeatFinitePartSchemeAgreement",
        "relative_heat_finite_part_scheme_independence_gate",
    ),
    "P0EFTJanusProgramPRelativeHeatFinitePartFamily4D.lean": (
        "RelativeHeatFinitePartFamilyData",
        "relativeHeatFinitePartMetricWeight",
        "relative_heat_finite_part_family_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianFinitePartDeterminant4D.lean": (
        "GlobalCandidateAHessianFinitePartDeterminantData4D",
        "globalCandidateAHessianFinitePartDeterminant",
        "global_candidateA_hessian_finitePart_determinant_gate",
    ),
    "P0EFTJanusProgramPRelativeZetaComparison4D.lean": (
        "RelativeZetaComparisonData",
        "relativeZetaDeterminant",
        "relative_zeta_comparison_gate",
    ),
    "P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.lean": (
        "RelativeHeatMellinZetaContinuationData",
        "relativeHeatMellinZetaCandidate",
        "relative_heat_mellin_zeta_continuation_gate",
    ),
    "P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.lean": (
        "RelativeZetaDeterminantFamilyData",
        "relativeZetaDeterminantCoordinate_parallel",
        "relative_zeta_determinant_connection_gate",
    ),
    "P0EFTJanusProgramPRelativeZetaFinitePartFamily4D.lean": (
        "RelativeZetaFinitePartFamilyComparisonData",
        "relativeZetaFinitePartPhase",
        "relative_zeta_finite_part_family_gate",
    ),
    "P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.lean": (
        "RelativeHeatMellinZetaFamilyData",
        "relativeHeatMellinZetaFamilyDeterminant",
        "relative_heat_mellin_zeta_family_gate",
    ),
    "P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D.lean": (
        "RelativeZetaLocalFamilyAtlasData",
        "relativeZetaTransition_cocycle",
        "relative_zeta_determinant_cocycle_gate",
    ),
    "P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D.lean": (
        "RelativeZetaDeterminantLineAtlasCertificate",
        "relative_zeta_determinant_line_atlas_gate",
    ),
    "P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D.lean": (
        "RelativeZetaCircleConnectionBridgeData",
        "relative_zeta_circle_connection_bridge_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianQuillenMetricAnchor4D.lean": (
        "globalCandidateAHessianQuillenMetricAnchor",
        "global_candidateA_hessian_quillen_metric_anchor_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianQuillenParallelSection4D.lean": (
        "globalCandidateAHessianQuillenParallelSection",
        "global_candidateA_hessian_quillen_parallel_section_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianZetaDeterminant4D.lean": (
        "GlobalCandidateAHessianZetaDeterminantData4D",
        "global_candidateA_hessian_zeta_determinant_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianZetaDeterminantAtlas4D.lean": (
        "GlobalCandidateAHessianZetaDeterminantAtlasData4D",
        "global_candidateA_hessian_zeta_determinant_atlas_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianQuillenFamilyBridge4D.lean": (
        "GlobalCandidateAHessianQuillenFamilyBridgeData4D",
        "global_candidateA_hessian_quillen_family_bridge_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianQuillenCertificate4D.lean": (
        "GlobalCandidateAHessianQuillenCertificate4D",
        "global_candidateA_hessian_quillen_certificate_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianQuillenClosure4D.lean": (
        "GlobalCandidateAHessianQuillenClosureCertificate4D",
        "global_candidateA_hessian_quillen_global_closure_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianQuillenFinalFrontier4D.lean": (
        "GlobalCandidateAHessianQuillenFinalFrontierData4D",
        "GlobalCandidateAHessianQuillenFinalFrontierCertificate4D",
        "global_candidateA_hessian_quillen_final_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianQuillenMellinFrontier4D.lean": (
        "GlobalCandidateAHessianQuillenMellinFrontierData4D",
        "global_candidateA_hessian_quillen_mellin_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianZetaQuillenFrontier4D.lean": (
        "global_candidateA_hessian_zeta_quillen_frontier_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-zeta-quillen.yml"
DOC = ROOT / "docs" / "hessian_global_01_zeta_quillen_frontier.md"


def has_decl(text: str, name: str) -> bool:
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:structure|def|abbrev|theorem|lemma)\s+{re.escape(name)}\b",
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
        print("Hessian zeta/Quillen audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian zeta/Quillen audit: OK")
    print("- intrinsic relative trace")
    print("- finite-part determinant, family metric and scheme independence")
    print("- heat-Mellin representation and parameter-uniform continuation")
    print("- complex zeta determinant and unitary phase")
    print("- transition cocycle and determinant-line atlas")
    print("- Candidate-A atlas and periodic metric anchor")
    print("- Quillen parallel section and global closure")
    print("- Mellin-generated coherent final frontier")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

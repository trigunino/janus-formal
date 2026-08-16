#!/usr/bin/env python3
"""Static audit of the post-H14 reduced exponential and relative trace layer."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteDefectReducedExponential4D.lean": (
        "finiteDefectReducedExponential",
        "finiteDefectReducedExponential_add",
        "finite_defect_reduced_exponential_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D.lean": (
        "finiteDimensional_of_compact_finiteDefectReducedExponential",
        "finite_defect_reduced_bounded_heat_no_go_gate",
    ),
    "P0EFTJanusProgramPSummableCompactOperatorExpansion4D.lean": (
        "SummableCompactOperatorExpansion",
        "summable_compact_operator_expansion_gate",
    ),
    "P0EFTJanusProgramPSummableRankOneOperatorExpansion4D.lean": (
        "SummableRankOneOperatorExpansion",
        "summable_rank_one_operator_expansion_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D.lean": (
        "FiniteDefectReducedRelativeHeatData",
        "finite_defect_reduced_relative_heat_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectReducedRelativeTrace4D.lean": (
        "FiniteDefectReducedRelativeTraceData",
        "finiteDefectReducedRelativeHeatTrace",
        "finite_defect_reduced_relative_trace_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D.lean": (
        "GlobalCandidateAAugmentedReducedExponentialCertificate4D",
        "global_candidateA_augmented_reduced_exponential_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponentialCompactNoGo4D.lean": (
        "globalCandidateAAugmentedReducedExponential_compact_implies_finiteDimensional",
        "global_candidateA_bounded_reduced_heat_no_go_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeHeat4D.lean": (
        "GlobalCandidateAAugmentedReducedRelativeHeatData4D",
        "global_candidateA_augmented_reduced_relative_heat_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeTrace4D.lean": (
        "GlobalCandidateAAugmentedReducedRelativeTraceData4D",
        "globalCandidateAAugmentedReducedRelativeHeatTrace",
        "global_candidateA_augmented_reduced_relative_trace_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianRelativeDeterminantFrontier4D.lean": (
        "GlobalCandidateARelativeDeterminantPrerequisites4D",
        "global_candidateA_relative_determinant_prerequisites_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianRelativeTraceFrontier4D.lean": (
        "GlobalCandidateARelativeTracePrerequisites4D",
        "global_candidateA_relative_trace_prerequisites_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-relative-trace.yml"


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

    docs = (
        ROOT / "docs" / "hessian_global_01_reduced_resolvent.md",
        ROOT / "docs" / "hessian_global_01_relative_trace_frontier.md",
    )
    for doc in docs:
        if not doc.is_file():
            errors.append(f"missing documentation: {doc.relative_to(ROOT)}")

    if errors:
        print("Reduced exponential/relative trace audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Reduced exponential/relative trace audit: OK")
    print("- exact bounded reduced exponential")
    print("- compact absolute-heat no-go")
    print("- summable compact relative expansion")
    print("- summable rank-one relative trace series")
    print("- honest determinant prerequisites")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

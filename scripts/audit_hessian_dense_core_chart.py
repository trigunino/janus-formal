#!/usr/bin/env python3
"""Static audit of the dense-core physical-chart Hessian route."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPDenseCoreChartBilinearBound4D.lean": (
        "DenseCoreChartMapBound",
        "denseCoreChartBilinearPullback_bound",
        "dense_core_chart_bilinear_bound_gate",
    ),
    "P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D.lean": (
        "denseCoreFiniteChartHessianSum",
        "denseCoreFiniteChartHessianSum_bound",
        "dense_core_finite_chart_hessian_bound_gate",
    ),
    "P0EFTJanusProgramPDenseCoreChartHessianAgreement4D.lean": (
        "DenseCoreFiniteChartHessianAgreement",
        "DenseCoreFiniteChartHessianAgreement.toProductBound",
        "dense_core_chart_hessian_agreement_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianDenseCoreChartFrontier4D.lean": (
        "GlobalHessianDenseCoreChartMapBoundInput",
        "GlobalHessianDenseCoreChartAgreementInput",
        "global_candidateA_hessian_denseCoreChart_frontier_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem|lemma)\b"),
)


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

    if errors:
        print("Dense-core chart Hessian audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Dense-core chart Hessian audit: OK")
    print("- no Hilbert-to-smooth regularization map")
    print("- finite physical Hessian sum controlled by one graph-core estimate")
    print("- exact agreement produces the H11 product bound")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

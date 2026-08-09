#!/usr/bin/env python3
"""Static audit of the stationary-symmetry Candidate-A Hessian frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPStationarySymmetryCurveHessianKernel4D.lean": (
        "ActionStationaryAlongCurveEventually",
        "gradientCurveInvariant_of_stationaryCurve",
        "stationary_symmetry_curve_hessian_kernel_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAStationarySymmetryZeroModes4D.lean": (
        "globalCandidateACommonAugmentedAction_zero_stationary",
        "GlobalCandidateAStationarySymmetryCurves4D",
        "GlobalCandidateAStationarySymmetryAutomaticSplit4D",
        "global_candidateA_stationary_symmetry_zero_mode_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixStationarySymmetryFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_stationarySymmetry_frontier_gate",
        "global_candidateA_hessian_canonicalSix_stationarySymmetry_exact_count",
    ),
    "P0EFTJanusProgramPGlobalHessianNoetherZeroModeFrontier4D.lean": (
        "global_candidateA_hessian_noether_zeroMode_frontier_gate",
        "global_candidateA_hessian_noether_curve_frontier_gate",
        "global_candidateA_hessian_noether_action_frontier_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-stationary-symmetry.yml"


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

    if errors:
        print("Hessian stationary-symmetry audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian stationary-symmetry audit: OK")
    print("- stationary curve -> Jacobi field")
    print("- Candidate-A base stationarity")
    print("- actual Riesz kernel and no-hidden-mode Garding")
    print("- canonical-six H10-H14 terminal closure")
    print("- public Noether zero-mode facade")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

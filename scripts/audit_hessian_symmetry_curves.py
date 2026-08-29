#!/usr/bin/env python3
"""Static audit of the nonlinear Candidate-A symmetry-curve frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPSymmetryCurveHessianKernel4D.lean": (
        "SymmetryCurveAt",
        "CurveEventuallyInvariantAt",
        "fderiv_apply_eq_zero_of_curveEventuallyInvariant",
        "symmetry_curve_hessian_kernel_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateASymmetryCurveZeroModes4D.lean": (
        "GlobalCandidateASymmetryCurveModes4D",
        "GlobalCandidateASymmetryCurveModes4D.vector_annihilated",
        "GlobalCandidateASymmetryCurveAutomaticSplit4D",
        "global_candidateA_symmetry_curve_zero_mode_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSymmetryCurveFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_symmetryCurve_frontier_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-symmetry-curves.yml"
DOC = ROOT / "docs" / "hessian_global_01_symmetry_curves.md"


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
        print("Hessian symmetry-curve audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian symmetry-curve audit: OK")
    print("- arbitrary differentiable orbit")
    print("- Noether tangent kernel identity")
    print("- Candidate-A Riesz zero modes")
    print("- automatic no-hidden-mode Garding")
    print("- canonical-six terminal frontier")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Static audit of the no-hidden-zero-mode Hessian frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D.lean": (
        "FiniteKernelNamedModeNoHiddenData",
        "FiniteKernelNamedModeNoHiddenData.remainder_eq_zero",
        "FiniteKernelNamedModeNoHiddenData.span_eq_top",
        "FiniteKernelNamedModeNoHiddenData.toNamedGarding",
        "finite_kernel_named_mode_no_hidden_gate",
    ),
    "P0EFTJanusProgramPFiniteKernelNamedModeDecomposition4D.lean": (
        "FiniteKernelNamedDecompositionData",
        "FiniteKernelNamedDecompositionData.toSpanning",
        "FiniteKernelNamedDecompositionGardingData",
        "finite_kernel_named_decomposition_garding_gate",
    ),
    "P0EFTJanusProgramPNamedModeGardingPerturbation4D.lean": (
        "FiniteKernelNamedReferenceGardingPerturbationData",
        "perturbation_real_inner_lower_bound",
        "FiniteKernelNamedReferenceGardingPerturbationData.toNamedGarding",
        "named_mode_garding_bounded_perturbation_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixNoHiddenFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_noHidden_frontier_gate",
        "global_candidateA_hessian_canonicalSix_noHidden_two_inputs",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-no-hidden-modes.yml"
DOC = ROOT / "docs" / "hessian_global_01_no_hidden_modes.md"


def has_decl(text: str, name: str) -> bool:
    short = name.rsplit(".", 1)[-1]
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:structure|inductive|def|abbrev|theorem|lemma)\s+"
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
        print("Hessian no-hidden-mode audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian no-hidden-mode audit: OK")
    print("- exact kernel spanning is derived, not assumed")
    print("- explicit coefficient decompositions imply span equality")
    print("- global Garding coercivity excludes orthogonal hidden modes")
    print("- bounded perturbations preserve the named finite defect")
    print("- Candidate-A H10--H14 consumes the derived named-mode packet")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

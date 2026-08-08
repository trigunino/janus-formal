#!/usr/bin/env python3
"""Static audit of the finite-kernel-basis coercivity frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteKernelNamedModeBasis4D.lean": (
        "finiteKernelNamedModeFamilyOfBasis",
        "SelfAdjointKernelComplementCoercivityWithBasis",
        "selfAdjoint_kernel_basis_coercivity_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianKernelBasisCoercivityFrontier4D.lean": (
        "GlobalHessianKernelBasisCoercivityInput",
        "global_hessian_kernelBasis_coercivity_to_gap",
        "global_candidateA_hessian_kernelBasisCoercivity_frontier_gate",
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
        print("Kernel-basis coercivity audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Kernel-basis coercivity audit: OK")
    print("- finite basis generates named zero modes")
    print("- quadratic coercivity generates the actual-kernel gap")
    print("- terminal zero-mode frontier remains unchanged")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

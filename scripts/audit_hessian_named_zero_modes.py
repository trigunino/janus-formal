#!/usr/bin/env python3
"""Static audit of the named-zero-mode coercivity route."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteKernelNamedModes4D.lean": (
        "FiniteKernelNamedModeFamily",
        "SelfAdjointKernelComplementGapWithNamedModes",
        "finite_kernel_named_modes_actual_gap_gate",
    ),
    "P0EFTJanusProgramPFiniteKernelNamedModeOperators4D.lean": (
        "finiteKernelNamedModeSynthesisLinearMap",
        "finiteKernelNamedModeSynthesisLinearMap_range",
        "finite_kernel_named_mode_synthesis_gate",
    ),
    "P0EFTJanusProgramPSelfAdjointKernelComplementCoercivity4D.lean": (
        "SelfAdjointKernelComplementCoercivityWithNamedModes",
        "SelfAdjointKernelComplementCoercivityWithNamedModes.toGapWithNamedModes",
        "selfAdjoint_named_kernel_coercivity_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem|lemma)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-named-zero-modes.yml"
DOC = ROOT / "docs" / "hessian_global_01_named_zero_modes.md"


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
        print("Named zero-mode Hessian audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Named zero-mode Hessian audit: OK")
    print("- explicit finite labels and ambient vectors")
    print("- synthesis image equals the actual kernel")
    print("- quadratic coercivity implies the actual-kernel gap")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

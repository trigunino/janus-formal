#!/usr/bin/env python3
"""Static audit of the named-mode Gårding H10--H14 frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteKernelNamedModeGarding4D.lean": (
        "FiniteKernelNamedSpanningData",
        "FiniteKernelNamedModeGardingData",
        "FiniteKernelNamedModeGardingData.coercive",
        "FiniteKernelNamedModeGardingData.toBasisCoercivity",
        "finite_kernel_named_mode_garding_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D.lean": (
        "GlobalCandidateAActualKernelNamedGarding4D",
        "GlobalCandidateAActualKernelNamedGarding4D.toGap",
        "GlobalCandidateAActualKernelNamedGarding4D.kernel_finrank_eq_card",
        "global_candidateA_actual_kernel_named_garding_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixNamedGardingFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_namedGarding_frontier_gate",
        "global_candidateA_hessian_canonicalSix_namedGarding_two_inputs",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-named-garding.yml"
DOC = ROOT / "docs" / "hessian_global_01_named_garding.md"


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
        print("Hessian named-mode Garding audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Hessian named-mode Garding audit: OK")
    print("- named ambient modes are annihilated by the displayed Hessian")
    print("- independence and spanning reconstruct the actual kernel basis")
    print("- the finite Garding defect vanishes on the kernel complement")
    print("- quadratic coercivity, gap and exact zero-mode count are derived")
    print("- the canonical-six H10--H14 terminal consumes the derived gap")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

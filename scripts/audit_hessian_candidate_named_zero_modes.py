#!/usr/bin/env python3
"""Static audit of the Candidate-A named zero-mode coercivity façade."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPGlobalCandidateAActualNamedZeroModeCoercivity4D.lean": (
        "GlobalCandidateAActualNamedZeroModeCoercivity4D",
        "globalCandidateAActualNamedZeroModeCoercivity_toGap",
    ),
    "P0EFTJanusProgramPGlobalHessianNamedZeroModeCoercivityFrontier4D.lean": (
        "GlobalHessianNamedZeroModeCoercivityInput",
        "global_hessian_namedZeroMode_coercivity_to_gap",
        "global_candidateA_hessian_namedZeroModeCoercivity_frontier_gate",
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
        print("Candidate-A named zero-mode audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Candidate-A named zero-mode audit: OK")
    print("- quadratic coercivity specialized to the actual augmented Hessian")
    print("- canonical conversion to the existing zero-mode frontier")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

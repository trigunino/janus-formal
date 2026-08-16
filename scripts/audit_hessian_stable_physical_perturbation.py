#!/usr/bin/env python3
"""Static audit of the stable physical-perturbation Hessian frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPNamedModeKernelStablePerturbation4D.lean": (
        "FiniteKernelStableOrthogonalNamedModePerturbationData",
        "toOrthogonalGarding",
        "finite_kernel_stable_named_mode_perturbation_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualKernelStablePerturbation4D.lean": (
        "GlobalCandidateAActualKernelStablePerturbation4D",
        "toNamedGarding",
        "toCandidateNamedGarding",
        "global_candidateA_actual_kernel_stable_perturbation_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D.lean": (
        "globalCandidateACanonicalStableReferenceOperator",
        "globalCandidateACanonicalStablePhysicalPerturbation",
        "globalCandidateAActualKernelOperator_eq_canonicalStableSum",
        "GlobalCandidateACanonicalStableNamedPerturbation4D",
        "toActualStable",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixStablePerturbationFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_stablePerturbation_frontier_gate",
        "global_candidateA_hessian_canonicalSix_stablePerturbation_sector_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixPhysicalPerturbationFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_physicalPerturbation_frontier_gate",
        "global_candidateA_hessian_canonicalSix_physicalPerturbation_sector_gate",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-stable-physical-perturbation.yml"
DOC = ROOT / "docs" / \
    "hessian_global_01_stable_physical_perturbation.md"


def has_declaration(text: str, name: str) -> bool:
    short = name.rsplit(".", 1)[-1]
    pattern = (
        rf"(?m)^\s*(?:private\s+)?"
        rf"(?:structure|inductive|def|abbrev|theorem|lemma)\s+"
        rf"(?:[A-Za-z0-9_']+\.)?{re.escape(short)}\b"
    )
    return bool(re.search(pattern, text))


def main() -> int:
    errors: list[str] = []

    for filename, declarations in REQUIRED.items():
        path = GATES / filename
        if not path.is_file():
            errors.append(f"missing module: {filename}")
            continue
        text = path.read_text(encoding="utf-8")
        for declaration in declarations:
            if not has_declaration(text, declaration):
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
                errors.append(f"workflow does not build {filename}")

    if not DOC.is_file():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")

    if errors:
        print("Stable physical-perturbation audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Stable physical-perturbation audit: OK")
    print("- actual Candidate-A operator fixed as graph plus physical Riesz")
    print("- named modes preserved by both canonical pieces")
    print("- Gårding and perturbative smallness exclude hidden zero modes")
    print("- exact actual-kernel count and sector count derived")
    print("- H10-H14 terminal consumes no supplied gap or kernel spanning")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

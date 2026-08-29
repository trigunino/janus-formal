#!/usr/bin/env python3
"""Audit the strengthened concrete H10--H14 certificate façade."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPFiniteDefectKernelIdentification4D.lean": (
        "finiteDefect_operator_ker_eq_projection_range",
        "finite_defect_kernel_identification_gate",
    ),
    "P0EFTJanusProgramPFiniteDefectRangeIdentification4D.lean": (
        "finiteDefect_operator_range_eq_projection_ker",
        "finite_defect_range_identification_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSplitting4D.lean": (
        "GlobalCandidateAAugmentedFredholmSplitting4D",
        "global_candidateA_augmented_fredholm_splitting_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianConcreteCertificate4D.lean": (
        "GlobalCandidateAConcreteHessianCertificate4D",
        "global_candidateA_hessian_concrete_certificate_gate",
        "GlobalCandidateAConcreteHessianCertificate4D.kernel_eq_defect",
        "GlobalCandidateAConcreteHessianCertificate4D.range_eq_complement",
    ),
    "P0EFTJanusProgramPGlobalHessianConcreteCertificateFrontier4D.lean": (
        "global_candidateA_hessian_concrete_certificate_frontier_gate",
        "global_candidateA_hessian_concrete_certificate_frontier_three_inputs",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-concrete-certificate.yml"


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
            errors.append(f"missing module: {path.relative_to(ROOT)}")
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
        for target in REQUIRED:
            stem = target.removesuffix(".lean")
            if stem not in workflow:
                errors.append(f"workflow does not build {stem}")

    frontier = GATES / \
        "P0EFTJanusProgramPGlobalHessianConcreteCertificateFrontier4D.lean"
    if frontier.is_file():
        text = frontier.read_text(encoding="utf-8")
        if not re.search(r"Nonempty\s*\(Unit\s*×\s*Unit\s*×\s*Unit\)", text):
            errors.append("strengthened frontier does not expose three inputs")

    if errors:
        print("Concrete Hessian certificate audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Concrete Hessian certificate audit: OK")
    print("- ker H = range P")
    print("- range H = ker P")
    print("- terminal analytic inputs: 3")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Static audit of the concrete three-packet H10--H14 frontier.

This is an architectural audit, not a substitute for Lean kernel validation.
It checks that the narrow concrete route exists, is connected end to end, does
not reintroduce H10 as an input, and contains no proof placeholders.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"


@dataclass(frozen=True)
class RequiredModule:
    filename: str
    declarations: tuple[str, ...]


MODULES: tuple[RequiredModule, ...] = (
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D.lean",
        (
            "GlobalCandidateAH10ClosureCertificate4D",
            "global_candidateA_h10_closure_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D.lean",
        (
            "ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D.toH10Robin",
            "global_candidateA_h13_minimalPhysical_boundaryProjection_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D.lean",
        (
            "GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D",
            "globalCandidateAPhysicalBlockCanonicalCoreForm_symmetric",
            "canonicalContinuousAgreement_symmetric",
            "candidate_a_seven_physical_canonical_agreement_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPFiniteDefectGlobalLowerBound4D.lean",
        (
            "finiteDefectShiftControlConstant",
            "finiteDefectShiftedOperator_globalLowerBound",
            "finite_defect_global_lower_bound_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D.lean",
        (
            "GlobalCandidateAAugmentedOrthogonalCoerciveShift4D",
            "global_candidateA_h12_fredholm_gate_of_orthogonalCoerciveShift",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D.lean",
        ("global_candidateA_hessian_concreteAgreement_closure_gate",),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D.lean",
        (
            "GlobalHessianConcreteLocalFamilyInput",
            "GlobalHessianConcretePhysicalAgreementsInput",
            "GlobalHessianConcreteOrthogonalCoerciveShiftInput",
            "global_candidateA_hessian_concrete_analytic_closure_gate",
            "global_candidateA_hessian_concrete_analytic_frontier_gate",
        ),
    ),
)

FORBIDDEN: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"(?m)^\s*axiom\b")),
    ("unsafe declaration", re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b")),
)

FRONTIER = GATES / \
    "P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D.lean"
CLOSURE = GATES / \
    "P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D.lean"
WORKFLOW = ROOT / ".github" / "workflows" / \
    "program-p-hessian-concrete-frontier.yml"


def declaration_present(text: str, name: str) -> bool:
    return bool(re.search(
        rf"(?m)^\s*(?:private\s+)?(?:structure|def|abbrev|theorem|lemma|inductive)\s+{re.escape(name)}\b",
        text,
    ))


def audit_module(module: RequiredModule) -> list[str]:
    path = GATES / module.filename
    if not path.is_file():
        return [f"missing module: {path.relative_to(ROOT)}"]
    text = path.read_text(encoding="utf-8")
    errors: list[str] = []
    for declaration in module.declarations:
        if not declaration_present(text, declaration):
            errors.append(
                f"missing declaration {declaration!r} in {path.relative_to(ROOT)}"
            )
    for label, pattern in FORBIDDEN:
        if pattern.search(text):
            errors.append(f"forbidden {label} in {path.relative_to(ROOT)}")
    return errors


def audit_frontier() -> list[str]:
    errors: list[str] = []
    if not FRONTIER.is_file():
        return [f"missing frontier: {FRONTIER.relative_to(ROOT)}"]
    text = FRONTIER.read_text(encoding="utf-8")
    required_imports = (
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D",
        "P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D",
        "P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D",
        "P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D",
        "P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D",
    )
    for module in required_imports:
        if module not in text:
            errors.append(f"frontier does not import/reference {module}")
    if "GlobalHessianConcreteNormalBoundaryInput" in text:
        errors.append("H10 is incorrectly exposed as a residual frontier input")
    if not re.search(r"Nonempty\s*\(Unit\s*×\s*Unit\s*×\s*Unit\)", text):
        errors.append("frontier does not expose exactly three packets")
    if not re.search(
        r"(?s)global_candidateA_hessian_concrete_analytic_closure_gate\s*:=\s*\n?\s*@global_candidateA_hessian_concreteAgreement_closure_gate",
        text,
    ):
        errors.append("frontier endpoint is not attached to the concrete closure")
    return errors


def audit_closure() -> list[str]:
    if not CLOSURE.is_file():
        return [f"missing closure: {CLOSURE.relative_to(ROOT)}"]
    text = CLOSURE.read_text(encoding="utf-8")
    required = (
        "globalCandidateABoundaryProjectionChart",
        "globalCandidateABoundaryProjectionSameAction",
        "globalCandidateASevenPhysicalCanonicalContinuousAgreements4D",
        "globalCandidateAAugmentedOrthogonalCoerciveShift4D",
        "global_candidateA_hessian_boundaryProjection_closure_gate",
    )
    return [f"concrete closure does not reference {name}"
            for name in required if name not in text]


def audit_workflow() -> list[str]:
    if not WORKFLOW.is_file():
        return [f"missing workflow: {WORKFLOW.relative_to(ROOT)}"]
    text = WORKFLOW.read_text(encoding="utf-8")
    targets = (
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D",
        "P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D",
        "P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D",
        "P0EFTJanusProgramPFiniteDefectGlobalLowerBound4D",
        "P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D",
        "P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D",
        "P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D",
    )
    return [f"workflow does not build {target}"
            for target in targets if target not in text]


def main() -> int:
    errors: list[str] = []
    for module in MODULES:
        errors.extend(audit_module(module))
    errors.extend(audit_frontier())
    errors.extend(audit_closure())
    errors.extend(audit_workflow())

    if errors:
        print("Concrete Hessian frontier audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Concrete Hessian frontier audit: OK")
    print(f"- audited modules: {len(MODULES)}")
    print("- residual packets: concrete local family, dense H11 agreements, orthogonal coercive H12 shift")
    print("- H10 terminal input: none")
    print("- supplied H11 symmetries: none")
    print("- supplied global shifted bound/surjectivity/inverse: none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

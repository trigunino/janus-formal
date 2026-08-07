#!/usr/bin/env python3
"""Static audit of the constructive H10--H14 Hessian frontier.

This audit is deliberately weaker than Lean kernel validation.  It verifies the
repository architecture that must be present before the focused builds can be
trusted:

* every constructive module exists;
* the public declarations expected by the terminal route are present;
* no new `sorry`, `admit`, `axiom` or `unsafe` declaration is introduced;
* the terminal façade imports the narrow H10, H11 and H12 routes;
* the preferred workflow mentions the terminal façade.

Exit status is non-zero on any violation.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
GATES = (
    ROOT
    / "JanusFormal"
    / "Branches"
    / "FundamentalGeometryPVariationalPrinciple"
    / "Gates"
)


@dataclass(frozen=True)
class RequiredModule:
    filename: str
    declarations: tuple[str, ...]


MODULES: tuple[RequiredModule, ...] = (
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D.lean",
        (
            "SameRealActionGermAt",
            "candidate_a_normal_boundary_same_action_germ_calculus_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryIntegrandGermClosure4D.lean",
        (
            "SameRealIntegrandGermAt",
            "candidate_a_normal_boundary_integrand_germ_closure_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussFormGerm4D.lean",
        (
            "SameCovariantAccelerationGermAt",
            "SameGaussSecondFormGermAt",
            "candidate_a_normal_boundary_gauss_form_germ_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryEventuallyEqGerms4D.lean",
        (
            "NormalBoundaryEventuallyEqGermData",
            "candidate_a_normal_boundary_eventuallyEq_terminal_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryRobinFromGerm4D.lean",
        ("candidate_a_normal_boundary_robin_from_germ_gate",),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D.lean",
        (
            "ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D",
            "global_candidateA_h13_minimalPhysical_h10RobinFamily_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D.lean",
        (
            "GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D",
            "candidate_a_seven_physical_canonical_extensions_gate",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointComplement4D.lean",
        (
            "GlobalCandidateAFaithfulAugmentedSelfAdjointComplement4D",
            "global_candidateA_h12_complement_of_selfAdjoint_obstruction",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalHessianH10RobinSelfAdjointClosure4D.lean",
        ("global_candidateA_hessian_h10Robin_selfAdjoint_closure_gate",),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalHessianTerminalConstructiveClosure4D.lean",
        (
            "global_candidateA_hessian_terminal_constructive_closure_gate",
            "global_candidateA_hessian_terminal_constructive_frontier_gate",
        ),
    ),
)

FORBIDDEN_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom declaration", re.compile(r"(?m)^\s*axiom\b")),
    ("unsafe declaration", re.compile(r"(?m)^\s*unsafe\s+(def|theorem)\b")),
)

TERMINAL_IMPORTS = (
    "P0EFTJanusProgramPGlobalCandidateANormalBoundaryEventuallyEqGerms4D",
    "P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinAdapters4D",
    "P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D",
    "P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointComplement4D",
    "P0EFTJanusProgramPGlobalHessianH10RobinSelfAdjointClosure4D",
)

WORKFLOWS = (
    ROOT / ".github" / "workflows" / "program-p-h10-h14-preferred-frontier.yml",
    ROOT / ".github" / "workflows" / "program-p-hessian-terminal-constructive.yml",
)


def declaration_present(text: str, name: str) -> bool:
    pattern = re.compile(
        rf"(?m)^\s*(?:private\s+)?(?:structure|def|abbrev|theorem|lemma|inductive)\s+{re.escape(name)}\b"
    )
    return bool(pattern.search(text))


def audit_module(module: RequiredModule) -> list[str]:
    errors: list[str] = []
    path = GATES / module.filename
    if not path.is_file():
        return [f"missing module: {path.relative_to(ROOT)}"]

    text = path.read_text(encoding="utf-8")
    for declaration in module.declarations:
        if not declaration_present(text, declaration):
            errors.append(
                f"missing declaration {declaration!r} in {path.relative_to(ROOT)}"
            )

    for label, pattern in FORBIDDEN_PATTERNS:
        if pattern.search(text):
            errors.append(f"forbidden {label} in {path.relative_to(ROOT)}")

    return errors


def audit_terminal_imports() -> list[str]:
    errors: list[str] = []
    path = GATES / "P0EFTJanusProgramPGlobalHessianTerminalConstructiveClosure4D.lean"
    if not path.is_file():
        return [f"missing terminal façade: {path.relative_to(ROOT)}"]

    text = path.read_text(encoding="utf-8")
    for module in TERMINAL_IMPORTS:
        if module not in text:
            errors.append(
                f"terminal façade does not import/reference required module {module}"
            )

    alias_pattern = re.compile(
        r"(?s)def\s+global_candidateA_hessian_terminal_constructive_closure_gate\s*:=\s*\n?\s*@global_candidateA_hessian_h10Robin_selfAdjoint_closure_gate"
    )
    if not alias_pattern.search(text):
        errors.append("terminal façade is not attached to the self-adjoint H14 gate")

    return errors


def audit_workflows() -> list[str]:
    errors: list[str] = []
    terminal_target = "P0EFTJanusProgramPGlobalHessianTerminalConstructiveClosure4D"
    found = False
    for path in WORKFLOWS:
        if not path.is_file():
            errors.append(f"missing workflow: {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        if terminal_target in text:
            found = True
    if not found:
        errors.append("no focused workflow builds the terminal constructive façade")
    return errors


def main() -> int:
    errors: list[str] = []
    for module in MODULES:
        errors.extend(audit_module(module))
    errors.extend(audit_terminal_imports())
    errors.extend(audit_workflows())

    if errors:
        print("Constructive Hessian audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Constructive Hessian audit: OK")
    print(f"- modules checked: {len(MODULES)}")
    print("- terminal route: H10 eventual germs -> H10 Robin family -> canonical H11 -> self-adjoint H12 -> H14")
    print("- forbidden placeholders: none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Static audit of the constructive H10--H14 Hessian frontier.

This audit is deliberately weaker than Lean kernel validation. It verifies the
repository architecture required by the preferred terminal route:

* the concrete H10 certificate exists and is not a terminal input;
* the six-block family and canonical seven-block extensions are present;
* the self-adjoint lower-bound shift route is present;
* the terminal façade is attached to the three-input lower-bound H14 gate;
* no new `sorry`, `admit`, `axiom` or `unsafe` declaration appears in the
  audited modules;
* a focused workflow builds the terminal façade.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

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
        "P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D.lean",
        (
            "GlobalCandidateAH10ClosureCertificate4D",
            "global_candidateA_h10_closure_gate",
        ),
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
        "P0EFTJanusProgramPSelfAdjointAntilipschitzSurjective4D.lean",
        (
            "selfAdjoint_bijective_of_antilipschitz",
            "selfAdjoint_surjective_of_antilipschitz",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D.lean",
        (
            "continuousLinearMap_antilipschitz_of_globalLowerBound",
            "selfAdjoint_surjective_of_globalLowerBound",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D.lean",
        (
            "GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D",
            "globalCandidateAAugmentedShiftedOperator_surjective_of_lowerBound",
            "global_candidateA_h12_fredholm_gate_of_selfAdjointLowerBoundShift",
        ),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalHessianH10RobinLowerBoundClosure4D.lean",
        ("global_candidateA_hessian_h10Robin_lowerBound_closure_gate",),
    ),
    RequiredModule(
        "P0EFTJanusProgramPGlobalHessianTerminalConstructiveClosure4D.lean",
        (
            "GlobalHessianTerminalLocalFamilyInput",
            "GlobalHessianTerminalPhysicalExtensionsInput",
            "GlobalHessianTerminalLowerBoundShiftInput",
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
    "P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D",
    "P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinAdapters4D",
    "P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D",
    "P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D",
    "P0EFTJanusProgramPGlobalHessianH10RobinLowerBoundClosure4D",
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
        r"(?s)def\s+global_candidateA_hessian_terminal_constructive_closure_gate\s*:=\s*\n?\s*@global_candidateA_hessian_h10Robin_lowerBound_closure_gate"
    )
    if not alias_pattern.search(text):
        errors.append("terminal façade is not attached to the lower-bound H14 gate")

    if "GlobalHessianTerminalNormalBoundaryInput" in text:
        errors.append("H10 is still exposed as a residual terminal input")

    frontier_pattern = re.compile(
        r"Nonempty\s*\(Unit\s*×\s*Unit\s*×\s*Unit\)"
    )
    if not frontier_pattern.search(text):
        errors.append("terminal façade does not expose exactly three inputs")

    return errors


def audit_workflows() -> list[str]:
    errors: list[str] = []
    targets = (
        "P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D",
        "P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D",
        "P0EFTJanusProgramPGlobalHessianH10RobinLowerBoundClosure4D",
        "P0EFTJanusProgramPGlobalHessianTerminalConstructiveClosure4D",
    )
    combined = ""
    for path in WORKFLOWS:
        if not path.is_file():
            errors.append(f"missing workflow: {path.relative_to(ROOT)}")
            continue
        combined += "\n" + path.read_text(encoding="utf-8")
    for target in targets:
        if target not in combined:
            errors.append(f"no focused workflow builds {target}")
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
    print("- terminal route: H10 theorem -> six-block family -> canonical H11 -> self-adjoint lower bound H12 -> H14")
    print("- terminal analytic inputs: 3")
    print("- forbidden placeholders: none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

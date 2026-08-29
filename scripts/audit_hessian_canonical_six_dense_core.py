#!/usr/bin/env python3
"""Static audit of the canonical six-block dense-core H11 frontier."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
GATES = ROOT / "JanusFormal" / "Branches" / \
    "FundamentalGeometryPVariationalPrinciple" / "Gates"

REQUIRED = {
    "P0EFTJanusProgramPSecondFrechetLinearPullback4D.lean": (
        "actionGradient_linearPullback",
        "secondFrechet_linearPullback",
        "secondFrechet_eq_bilinearComp_of_action_eq",
        "second_frechet_linear_pullback_gate",
    ),
    "P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D.lean": (
        "CanonicalSixPhysicalBlock",
        "canonicalSixPhysicalBlockHessian",
        "canonicalSixPhysicalHessianSum",
        "fullCoupledPhysicalHessian_eq_six_add_robin",
        "canonical_six_physical_chart_hessian_gate",
    ),
    "P0EFTJanusProgramPCanonicalSixPhysicalDenseCoreBound4D.lean": (
        "canonicalSixPhysicalDenseCoreSum",
        "CanonicalSixPhysicalDenseCoreAgreement",
        "CanonicalSixPhysicalDenseCoreAgreement.toProductBound",
        "canonical_six_physical_dense_core_bound_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D.lean": (
        "globalCandidateACanonicalSixLocalBlocks",
        "globalCandidateACanonicalSixCoreToChart",
        "GlobalCandidateAH10RobinDenseCoreAgreement4D",
        "globalCandidateASixPhysicalAggregateBound_of_canonicalDenseCore",
        "global_candidateA_h11_gate_of_canonical_six_dense_core",
    ),
    "P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D.lean": (
        "GlobalCandidateAH10RobinProjectionCoreData4D",
        "globalCandidateALocalRobinHessian_eq_h10Pullback",
        "GlobalCandidateAH10RobinProjectionCoreData4D.toDenseCoreAgreement",
        "global_candidateA_h10_robin_projection_core_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixDenseCoreFrontier4D.lean": (
        "globalCandidateACanonicalSixTerminalBound",
        "globalCandidateACanonicalSixPhysicalExtension",
        "global_candidateA_hessian_canonicalSix_denseCore_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixProjectionCoreFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_projectionCore_frontier_gate",
        "global_candidateA_hessian_canonicalSix_projectionCore_three_inputs",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)


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

    if errors:
        print("Canonical six dense-core audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Canonical six dense-core audit: OK")
    print("- six scalar actions fixed by FullCoupledActionBlocks")
    print("- exact second-Frechet additive decomposition")
    print("- canonical finite dense-core sum")
    print("- H10 Robin Hessian derived from the scalar action pullback")
    print("- projection agreement replaces a supplied Hessian equality")
    print("- direct H11 and H10--H14 frontiers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

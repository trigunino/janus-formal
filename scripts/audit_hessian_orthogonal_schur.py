#!/usr/bin/env python3
"""Static audit for the orthogonal finite-mode Schur H10--H14 frontier."""

from __future__ import annotations

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

REQUIRED: dict[str, tuple[str, ...]] = {
    "P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D.lean": (
        "finiteModeOrthogonalDecomposition",
        "FiniteModeOrthogonalSchurDecompositionData",
        "finite_mode_orthogonal_schur_decomposition_gate",
    ),
    "P0EFTJanusProgramPFiniteModeOrthogonalSchurBasis4D.lean": (
        "finiteModeContinuousEquivOfBasis",
        "FiniteModeOrthogonalSchurBasisData",
        "finite_mode_orthogonal_schur_basis_gate",
    ),
    "P0EFTJanusProgramPFiniteModeOrthogonalSchurNamedVectors4D.lean": (
        "finiteModeNamedSubspace",
        "FiniteModeOrthogonalSchurNamedVectorsData",
        "finite_mode_orthogonal_schur_named_vectors_gate",
    ),
    "P0EFTJanusProgramPFiniteModeSchurNamedKernelModes4D.lean": (
        "FiniteModeSchurNamedKernelBasisData",
        "coordinates",
        "toNamedModeFamily",
        "finite_mode_schur_named_kernel_modes_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurBlock4D.lean": (
        "GlobalCandidateAActualOrthogonalSchurData4D",
        "global_candidateA_actual_orthogonal_schur_block_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurBasis4D.lean": (
        "GlobalCandidateAActualOrthogonalSchurBasisData4D",
        "global_candidateA_actual_orthogonal_schur_basis_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedVectors4D.lean": (
        "GlobalCandidateAActualOrthogonalSchurNamedVectorsData4D",
        "global_candidateA_actual_orthogonal_schur_named_vectors_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualSchurNamedZeroMode4D.lean": (
        "GlobalCandidateAActualSchurNamedZeroModeData4D",
        "namedFamily",
        "namedGap",
        "global_candidateA_actual_schur_named_zeroMode_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedKernel4D.lean": (
        "GlobalCandidateAActualOrthogonalSchurNamedKernelData4D",
        "toNamedZeroModeData",
        "global_candidateA_actual_orthogonal_schur_named_kernel_gate",
    ),
    "P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurDeterminant4D.lean": (
        "globalCandidateAOrthogonalSchurDeterminant",
        "GlobalCandidateAActualOrthogonalSchurDeterminantData4D",
        "global_candidateA_actual_orthogonal_schur_determinant_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedVectorsFrontier4D.lean": (
        "global_candidateA_hessian_canonicalSix_orthogonalSchurNamedVectors_frontier_gate",
        "global_candidateA_hessian_orthogonalSchurNamedVectors_kernel_finrank_eq",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D.lean": (
        "globalCandidateACanonicalSixSchurNamedPhysicalExtension",
        "globalCandidateACanonicalSixSchurNamedActualGap",
        "global_candidateA_hessian_canonicalSix_schurNamedZeroMode_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixSchurSectorModesFrontier4D.lean": (
        "GlobalCandidateAOrthogonalSchurSectorModesData4D",
        "kernel_finrank_eq_sum",
        "global_candidateA_hessian_canonicalSix_schurSectorModes_frontier_gate",
    ),
    "P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedDeterminantFrontier4D.lean": (
        "GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D",
        "globalCandidateAHessianNamedOrthogonalSchurDeterminant",
        "global_candidateA_hessian_canonicalSix_namedOrthogonalSchurDeterminant_frontier_gate",
        "global_candidateA_hessian_namedOrthogonalSchurDeterminant_kernel_zero",
    ),
}

FORBIDDEN = (
    re.compile(r"\bsorry\b"),
    re.compile(r"\badmit\b"),
    re.compile(r"(?m)^\s*axiom\b"),
    re.compile(r"(?m)^\s*unsafe\s+(?:def|theorem)\b"),
)

WORKFLOW = ROOT / ".github" / "workflows" / "program-p-hessian-orthogonal-schur.yml"
DOC = ROOT / "docs" / "hessian_global_01_orthogonal_schur.md"


def has_declaration(text: str, name: str) -> bool:
    short = name.rsplit(".", 1)[-1]
    pattern = re.compile(
        rf"(?m)^\s*(?:private\s+)?(?:noncomputable\s+)?"
        rf"(?:structure|inductive|def|abbrev|theorem|lemma)\s+"
        rf"(?:[A-Za-z0-9_']+\.)?{re.escape(short)}\b"
    )
    return bool(pattern.search(text))


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
        for forbidden in FORBIDDEN:
            if forbidden.search(text):
                errors.append(f"forbidden placeholder/declaration in {filename}")

    if not DOC.is_file():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")

    if not WORKFLOW.is_file():
        errors.append(f"missing workflow: {WORKFLOW.relative_to(ROOT)}")
    else:
        workflow = WORKFLOW.read_text(encoding="utf-8")
        for filename in REQUIRED:
            module = filename.removesuffix(".lean")
            if module not in workflow:
                errors.append(f"workflow does not reference {module}")

    if errors:
        print("Orthogonal Schur Hessian audit: FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Orthogonal Schur Hessian audit: OK")
    print("- finite physical vectors generate their own mode subspace and basis")
    print("- Hilbert projection supplies the canonical orthogonal complement")
    print("- the displayed Hessian supplies all four Schur blocks")
    print("- a finite basis of ker S reconstructs concrete actual zero modes")
    print("- named zero modes span exactly ker H and admit sector counts")
    print("- complementary-block invertibility yields the actual-kernel package")
    print("- a finite determinant yields the zero-mode-free full Green operator")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

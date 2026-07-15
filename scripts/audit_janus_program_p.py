#!/usr/bin/env python3
"""Integrity checks for the new Program P and P-F Lean gates."""

from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
GATE_ROOT = Path(
    "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple/Gates"
)

PROGRAM_P_GATES = {
    "P0EFTJanusCoupledSectorHelmholtzSelection.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        ("theorem helmholtz_pt_realizability_iff",),
    ),
    "P0EFTJanusParentBulkHelmholtzReciprocity.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        ("theorem parent_bulk_helmholtz_reciprocity_synthesis",),
    ),
    "P0EFTJanusAnomalyHelmholtzIndependence.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem every_filter_truth_pattern_is_realized",
            "theorem every_anomaly_variational_truth_pattern_is_realized",
        ),
    ),
    "P0EFTJanusCompatibilityBridgeHierarchy.lean": (
        "JanusFormal/Branches/FundamentalGeometryPFCompatibilityHelmholtz.lean",
        ("theorem abstract_compatibility_variational_synthesis",),
    ),
    "P0EFTJanusFiniteRankPolynomialHelmholtz.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem finite_rank_polynomial_helmholtz_iff",
            "theorem reconstructed_potential_fderiv_apply",
            "theorem eulerVector_fderiv",
            "theorem eulerVector_fderiv_pairing_self_adjoint",
            "theorem actual_finite_helmholtz_iff_coefficient_helmholtz",
            "theorem actual_finite_helmholtz_iff_actual_polynomial_gradient",
            "theorem actual_finite_helmholtz_hasFDerivAt_polynomial_primitive",
        ),
    ),
    "P0EFTJanusConvexHelmholtzReconstruction.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem action_gradient_helmholtz_at",
            "theorem convex_open_helmholtz_reconstruction",
            "theorem radial_action_hasFDerivAt",
            "theorem convex_actions_same_euler_differ_by_constant",
            "theorem convex_actions_same_euler_eqOn_of_eq_at_base",
        ),
    ),
    "P0EFTJanusLinearGaugeNoetherReconstruction.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem translation_gauge_invariant_of_hasFDerivAt_horizontal",
            "theorem normalized_gauge_invariant_radial_reconstruction",
        ),
    ),
    "P0EFTJanusFiniteRankParentSchurHelmholtz.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem finite_rank_parent_schur_helmholtz_synthesis",
            "theorem finite_rank_parent_actual_variational_synthesis",
            "theorem parent_action_hasDerivAt_bulk",
            "theorem reduced_action_fderiv",
            "theorem reduced_hessian_operator_fderiv",
            "theorem parent_action_sub_reduced_action_eq_square",
            "theorem stationary_bulk_unique_global_minimizer",
            "theorem stationary_bulk_unique_global_maximizer",
        ),
    ),
}


def assert_program_p_gate_integrity(repo_root: Path = REPO_ROOT) -> None:
    """Require key declarations, facade imports, and placeholder-free proofs."""
    facades: dict[str, str] = {}

    for filename, (facade_path, declarations) in PROGRAM_P_GATES.items():
        source = (repo_root / GATE_ROOT / filename).read_text(encoding="utf-8")
        for declaration in declarations:
            if declaration not in source:
                raise AssertionError(f"missing Program P declaration: {declaration}")
        if re.search(r"\b(?:sorry|admit|axiom)\b", source):
            raise AssertionError(f"proof placeholder found in {filename}")

        facade = facades.setdefault(
            facade_path,
            (repo_root / facade_path).read_text(encoding="utf-8"),
        )
        gate_import = f"Gates.{filename.removesuffix('.lean')}"
        if gate_import not in facade:
            raise AssertionError(f"Program facade omits {filename}")

    primary_facade = facades[
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean"
    ]
    for status in (
        "pcFiniteRankActualHelmholtzIffActualPolynomialGradientProved",
        "pcConditionalLinearGaugeNoetherReconstructionProved",
    ):
        if (
            f"{status} : Prop" not in primary_facade
            or f"s.{status}" not in primary_facade
        ):
            raise AssertionError(f"Program P facade omits status: {status}")


def run_audit() -> None:
    assert_program_p_gate_integrity()
    print("Program P/P-F integrity audit: all checks passed")


if __name__ == "__main__":
    run_audit()

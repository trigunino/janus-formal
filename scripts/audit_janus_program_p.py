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
    "P0EFTJanusFrechetPullbackSecondVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPFCompatibilityHelmholtz.lean",
        (
            "theorem pulledBackAction_second_fderiv_apply",
            "theorem pulledBackAction_second_fderiv_at_critical",
        ),
    ),
    "P0EFTJanusFrechetPullbackHelmholtz.lean": (
        "JanusFormal/Branches/FundamentalGeometryPFCompatibilityHelmholtz.lean",
        (
            "theorem sourceSecondVariation_symmetric",
            "theorem jacobianPullbackHessian_symmetric_at_critical",
        ),
    ),
    "P0EFTJanusFrechetPullbackGaugeDegeneracy.lean": (
        "JanusFormal/Branches/FundamentalGeometryPFCompatibilityHelmholtz.lean",
        (
            "theorem pulledBackAction_fderiv_eq_zero_at_target_critical",
            "theorem pulledBackAction_second_fderiv_annihilates_jacobian_kernel",
            "theorem pulledBackAction_second_fderiv_annihilates_generated_gauge",
        ),
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
            "theorem hasFDerivAt_eulerGradientFunctional_implies_formal_gradient",
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
            "theorem translation_gauge_invariant_iff_euler_horizontal",
            "theorem normalized_gauge_invariant_radial_reconstruction",
        ),
    ),
    "P0EFTJanusNonlinearGaugeFlowNoether.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem flow_gauge_invariant_iff_euler_annihilates_generator",
            "theorem normalized_flow_gauge_invariant_radial_reconstruction",
        ),
    ),
    "P0EFTJanusGaugeOrbitDescent.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem orbitRel_trans",
            "theorem flow_gauge_invariant_unique_orbit_factor",
            "theorem radial_reconstruction_unique_orbit_factor",
        ),
    ),
    "P0EFTJanusGaugeOrbitInvariantEquiv.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem pullbackOrbitFunction_invariant",
            "def orbitFunctionsEquivFlowInvariantFunctions",
            "def orbitActionsEquivFlowGaugeInvariant",
        ),
    ),
    "P0EFTJanusPTFlatBimetricVariationalBridge.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem proportionalInteractionEnergy_hasDerivAt",
            "theorem proportionalInteractionForce_hasDerivAt_symmetric_point",
            "theorem symmetric_hessian_eq_twelve_fp_mass",
            "theorem proportionalInteractionEnergy_second_deriv_symmetric_point",
            "theorem symmetric_point_unique_positive_global_minimizer",
        ),
    ),
    "P0EFTJanusReducedTwoMetricBoundaryFirstVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem reducedInteractionAction_on_unit_plus",
            "theorem reducedInteractionAction_exchange",
            "theorem reducedTwoMetricAction_hasFDerivAt_canonical",
            "theorem reducedTwoMetricAction_line_hasDerivAt",
            "theorem reduced_stationarity_iff_euler_components_zero",
            "theorem unspecified_boundary_can_stationarize_any_scale_pair",
        ),
    ),
    "P0EFTJanusReducedTwoMetricEulerNoether.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem reducedInteractionAction_hasFDerivAt",
            "theorem full_stationarity_iff_both_euler_zero",
            "theorem diagonal_variation_sees_only_euler_sum",
            "theorem sign_linked_variation_sees_euler_difference",
            "theorem diagonal_noether_of_translation_invariance",
            "theorem reducedInteractionAction_diagonal_noether",
        ),
    ),
    "P0EFTJanusReducedBimetricQuadraticFrechetSpectrum.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem reducedQuadraticAction_hasFDerivAt",
            "theorem reducedQuadraticGradient_hasFDerivAt",
            "theorem reducedQuadraticAction_second_fderiv",
            "theorem conditional_reduced_hessian_positive",
            "theorem interaction_hessian_kernel_is_diagonal",
            "theorem relativeSectorHessian_positive",
            "theorem published_kappa_minus_one_has_negative_actual_hessian_direction",
        ),
    ),
    "P0EFTJanusTwoSectorBulkBoundaryFrechetVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem sectorAction_hasFDerivAt",
            "theorem sectorAction_line_hasDerivAt",
            "theorem sectorFirstVariation_annihilates_iff_bulk_boundary_balance",
            "theorem sectorStationaryAt_iff_bulk_boundary_balance",
            "theorem nonzero_boundary_flux_blocks_sector_stationarity",
            "theorem twoSectorAction_hasFDerivAt",
            "theorem twoSectorAction_line_hasDerivAt",
            "theorem twoSectorStationaryAt_iff_bulk_boundary_balance",
            "theorem nonzero_boundary_flux_blocks_two_sector_stationarity",
        ),
    ),
    "P0EFTJanusBoundaryCountertermHelmholtz.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem boundaryCounterterm_hasFDerivAt",
            "theorem completedBoundaryAction_hasFDerivAt_zero",
            "theorem completedSectorAction_hasFDerivAt_bulk",
            "theorem normalized_boundaryCounterterm_unique",
            "theorem actual_smooth_counterterm_implies_helmholtz_at",
            "theorem nonhelmholtz_flux_blocks_smooth_counterterm",
        ),
    ),
    "P0EFTJanusInducedFieldVariationNoDoubleCounting.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem jointEuler_comp_inducedGraphDerivative",
            "theorem inducedAction_hasFDerivAt",
            "theorem independentlyStationary_implies_constrainedStationary",
            "theorem cancellationRestrictedAction_fderiv",
            "theorem cancellation_bulkPartial_ne_zero",
            "theorem cancellation_inducedPartial_ne_zero",
            "theorem constrained_stationarity_does_not_imply_independent",
        ),
    ),
    "P0EFTJanusReducedCrossMatterIntegrability.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem crossEuler_hasFDerivAt",
            "theorem common_action_forces_cross_blocks_adjoint",
            "theorem commonCrossAction_hasFDerivAt",
            "theorem cross_blocks_adjoint_iff_common_action",
            "theorem nonadjoint_cross_blocks_no_common_action",
            "theorem metric_cross_mismatch_no_common_action",
        ),
    ),
    "P0EFTJanusNonlinearCrossDensityHelmholtz.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem blockDerivativeReciprocityAt_iff_helmholtzJacobianAt",
            "theorem blockDerivativeReciprocityOn_iff_helmholtzJacobianOn",
            "theorem open_convex_block_reciprocity_reconstructs_normalized_action",
            "theorem normalized_common_action_unique_on_domain",
            "theorem global_common_action_forces_block_reciprocity",
            "theorem failed_plus_minus_block_no_global_common_action",
        ),
    ),
    "P0EFTJanusReducedDiagonalNoetherExchangeBalance.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem diagonal_noether_combined_balance",
            "theorem combined_bulk_balance_eq_negative_boundary_flux",
            "theorem separate_conservation_iff_zero_exchange_and_boundary",
            "theorem zero_boundary_separate_conservation_iff_zero_exchange",
            "theorem exact_counterexample_sector_balances",
            "theorem combined_balance_does_not_imply_separate_conservation",
        ),
    ),
    "P0EFTJanusDiagonalGaugeNoetherIdentity.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem action_gaugeLine_hasDerivAt",
            "theorem infinitesimal_invariance_at_iff_euler_bianchi_annihilation",
            "theorem infinitesimal_invariance_iff_formalAdjoint_bianchi_constraint",
            "theorem formalAdjoint_constraint_closed_under_parameter_map",
            "theorem combined_identity_does_not_imply_separate_sector_identities",
        ),
    ),
    "P0EFTJanusProportionalBranchTransverseNoGo.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem extensions_agree_on_proportional_branch",
            "theorem proportional_branch_does_not_determine_transverse_curvature",
            "theorem extensions_differ_off_proportional_branch",
        ),
    ),
    "P0EFTJanusProportionalBranchHigherOrderNoGo.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem transverse_first_derivatives_agree_on_branch",
            "theorem transverse_hessians_agree_on_branch",
            "theorem branch_and_transverse_twoJet_do_not_determine_nonlinear_extension",
        ),
    ),
    "P0EFTJanusFrechetPullbackQuotientHessian.lean": (
        "JanusFormal/Branches/FundamentalGeometryPFCompatibilityHelmholtz.lean",
        (
            "theorem quotientHessian_mkQ",
            "theorem quotientHessian_unique",
            "theorem actualPullbackHessian_descends_to_gauge_quotient",
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
        "paPTFlatProportionalActualVariationalStabilityProved",
        "paReducedTwoMetricActualBoundaryVariationProved",
        "paConditionalReducedBimetricFrechetStabilityProved",
        "paReducedPublishedKappaMinusOneKineticNoGoProved",
        "paTwoSectorBulkBoundaryFrechetVariationProved",
        "paBoundaryCountertermHelmholtzCompletionProved",
        "paInducedFieldVariationNoDoubleCountingProved",
        "paProportionalBranchTransverseNonuniquenessProved",
        "paProportionalBranchTransverseTwoJetNonuniquenessProved",
        "pcFiniteRankActualHelmholtzIffActualPolynomialGradientProved",
        "pcConditionalLinearGaugeNoetherReconstructionProved",
        "pcConditionalLinearGaugeNoetherIffProved",
        "pcConditionalNonlinearGaugeFlowNoetherIffProved",
        "pcConditionalNonlinearGaugeInvariantRadialReconstructionProved",
        "pcGaugeOrbitQuotientDescentProved",
        "pcGaugeOrbitInvariantFunctionEquivalenceProved",
        "pcReducedTwoMetricEulerNoetherProved",
        "pcReducedCrossMatterIntegrabilityIffProved",
        "pcNonlinearCrossDensityHelmholtzReconstructionProved",
        "pcReducedDiagonalNoetherBoundaryExchangeProved",
        "pcDiagonalGaugeNoetherConstraintProved",
    ):
        if (
            primary_facade.count(f"{status} : Prop") != 1
            or primary_facade.count(f"s.{status}") != 1
        ):
            raise AssertionError(f"Program P facade omits status: {status}")

    pf_facade = facades[
        "JanusFormal/Branches/FundamentalGeometryPFCompatibilityHelmholtz.lean"
    ]
    for status in (
        "actualFrechetSecondVariationFormulaProved",
        "actualFrechetPullbackHelmholtzSymmetryProved",
        "actualFrechetPullbackGaugeDegeneracyProved",
        "actualFrechetPullbackQuotientHessianDescentProved",
    ):
        if (
            pf_facade.count(f"{status} : Prop") != 1
            or pf_facade.count(f"s.{status}") != 1
        ):
            raise AssertionError(f"Program P-F facade omits status: {status}")


def run_audit() -> None:
    assert_program_p_gate_integrity()
    print("Program P/P-F integrity audit: all checks passed")


if __name__ == "__main__":
    run_audit()

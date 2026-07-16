#!/usr/bin/env python3
"""Integrity checks for the new Program P and P-F Lean gates."""

from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
GATE_ROOT = Path(
    "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple/Gates"
)
D10_GATE_ROOT = Path(
    "JanusFormal/Branches/FundamentalGeometryD10QuillenAnomaly/Gates"
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
    "P0EFTJanusExplicitReciprocalCrossDensities.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem spectralPotential_reciprocity",
            "theorem crossDensities_matter_independent",
            "theorem two_M30_density_slots_eq_one_common_interaction",
        ),
    ),
    "P0EFTJanusExplicitReciprocalCrossDensityFrechet.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem spectralPotential_hasFDerivAt",
            "theorem spectralPotential_second_fderiv",
            "theorem commonInteractionGradient_helmholtzJacobianAt",
            "theorem commonInteractionGradient_ptFlat_proportionalSpectrum",
        ),
    ),
    "P0EFTJanusSpectralInteractionHessianIndefinite.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem nonzero_mixed01_forces_spectral_interaction_indefinite",
            "theorem positiveSemidefinite_forces_mixed01_zero",
            "theorem positive_ptFlat_cone_spectral_interaction_indefinite",
        ),
    ),
    "P0EFTJanusExplicitCandidatePointwiseEuler.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem candidatePointwiseAction_hasFDerivAt",
            "theorem candidatePointwiseEuler_hasFDerivAt",
            "theorem candidatePointwiseHessian_symmetric",
            "theorem candidatePointwiseEuler_helmholtzJacobianAt",
            "theorem candidatePointwiseStationary_iff_euler_components",
            "theorem interaction_matter_cross_hessian_vanishes",
        ),
    ),
    "P0EFTJanusMatrixSquareRootInteractionDensity.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem matrixSpectralPotential_diagonal",
            "theorem matrixSpectralPotential_conjugate",
            "structure SquareRootBranch",
            "structure SquareRootPointData",
            "theorem sqrt_abs_det_minus_eq_sqrt_abs_det_plus_mul_det_root",
            "theorem diagonalizable_volumeRatio_is_metric_measure_ratio",
            "theorem matrixSpectralPotential_of_diagonalizable_root",
            "def matrixCommonInteractionDensity",
            "theorem matrixCommonInteractionDensity_of_diagonal_root",
            "theorem diagonalizable_two_M30_slots_eq_matrixCommonInteractionDensity",
        ),
    ),
    "P0EFTJanusMatrixSquareRootFrechetSylvester.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem squareMap_hasFDerivAt",
            "theorem squareMap_second_fderiv_apply",
            "structure SylvesterInverseWitness",
            "theorem squareRoot_derivative_equation",
            "theorem differentiable_squareRoot_fderiv",
        ),
    ),
    "P0EFTJanusPositiveDiagonalSylvesterInverse.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem positiveDiagonalDomain_isOpen",
            "theorem diagonalSylvesterInverse_left",
            "theorem diagonalSylvesterInverse_right",
            "def positiveDiagonalSylvesterInverseWitness",
            "theorem positiveDiagonal_squareRoot_fderiv",
        ),
    ),
    "P0EFTJanusCoDiagonalLorentzRootChart.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem lorentzMetricInverse_mul_metric",
            "theorem rootMatrix_square_eq_relativeMetric",
            "theorem rootMatrix_det_pos",
            "theorem positiveDiagonalRoot_unique",
            "def coDiagonalSquareRootPointData",
            "def coDiagonalSylvesterInverseWitness",
            "theorem coDiagonal_squareRoot_hasFDerivAt",
        ),
    ),
    "P0EFTJanusCoDiagonalLorentzRootFirstDerivative.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem ambientPositiveScaleDomain_isOpen",
            "theorem ambientPositiveScalePairDomain_isOpen",
            "theorem ambientLorentzMetric_hasFDerivAt",
            "theorem ambientLorentzMetricInverse_hasFDerivAt",
            "theorem ambientRootMatrix_hasFDerivAt",
            "theorem ambientRelativeMetric_hasFDerivAt",
            "theorem ambient_squareRootIdentity_fderiv",
            "theorem explicitCoDiagonalRoot_hasFDerivAt",
            "theorem ambientRootMatrixDerivative_eq_explicitSylvester",
        ),
    ),
    "P0EFTJanusCoDiagonalInteractionDensityFrechet.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def coDiagonalInteractionDensity",
            "theorem ambientPlusMetricVolume_hasFDerivAt",
            "theorem coDiagonalSpectralPotential_hasFDerivAt",
            "theorem coDiagonalSpectralPotentialDerivative_eq_explicitSylvester",
            "theorem coDiagonalInteractionDensity_hasFDerivAt",
            "theorem coDiagonalInteractionDensityDerivative_apply",
            "theorem coDiagonalInteractionDensity_eq_pointwiseCandidateA",
        ),
    ),
    "P0EFTJanusDiagonalReparametrizationDensityNoether.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure CandidateDensityCurve",
            "theorem candidateDensity_hasDerivAt",
            "theorem affineParameterPullback_parameter_hasDerivAt",
            "theorem candidateDensityPullbackCurve_hasDerivAt",
            "theorem densityNoetherPrimitive_hasDerivAt",
            "theorem exactDensityEndpointLedger_totalShift_zero",
        ),
    ),
    "P0EFTJanusFourDimensionalDensityLieDerivativeNoether.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def affineFlow",
            "theorem affineFlow_hasFDerivAt",
            "theorem jacobianDeterminant_exact_expansion",
            "theorem jacobianDeterminant_hasDerivAt",
            "structure DifferentiableScalarDensity",
            "theorem densityPullbackCurve_hasDerivAt",
            "theorem densityFluxComponent_coordinateLine_hasDerivAt",
            "theorem coordinateFluxDivergence_eq_densityLieDerivative",
            "theorem densityPullbackCurve_hasDerivAt_coordinateFluxDivergence",
        ),
    ),
    "P0EFTJanusLinearizedEinsteinBianchiSymbol.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure SymmetricPerturbation",
            "def linearizedEinsteinSymbol",
            "theorem linearizedEinsteinSymbol_symmetric",
            "def einsteinSymbolDivergence",
            "theorem linearizedEinsteinSymbol_bianchi",
            "def pureGaugePerturbation",
            "theorem linearizedEinsteinSymbol_pureGauge_eq_zero",
        ),
    ),
    "P0EFTJanusMatrixDiagonalGaugeNoether.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem pointwiseInteractionScalar_diagonal_invariant",
            "theorem pointwiseInteractionDensity_diagonal_invariant",
            "theorem independent_frame_interaction_counterexample",
            "theorem conjugationCurve_hasDerivAt",
            "theorem matrixInteraction_noether_pairing",
        ),
    ),
    "P0EFTJanusMatrixInteractionFrechetNoether.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem determinant_hasFDerivAt",
            "theorem matrixElementary2_hasFDerivAt",
            "theorem matrixElementary3_hasFDerivAt",
            "theorem matrixSpectralPotential_hasFDerivAt",
            "theorem explicit_matrixInteraction_noether_pairing",
        ),
    ),
    "P0EFTJanusMatrixInteractionDensityCovariance.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem metricVolume_diagonal_weight",
            "theorem frame_det_ne_zero",
            "theorem abs_det_inverse_eq_inv_abs_det_frame",
            "theorem pointwiseInteractionDensity_diagonal_weight",
            "theorem pointwiseInteractionDensity_inverseJacobian_compensated",
        ),
    ),
    "P0EFTJanusFiniteFieldLocalFrameGauge.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def localDiagonalFrameAction",
            "def finiteInteractionAction",
            "theorem localInteractionDensity_inverseJacobian_compensated",
            "theorem finiteInteractionAction_localDiagonal_invariant",
            "theorem independent_sheet_frames_not_a_local_gauge_symmetry",
        ),
    ),
    "P0EFTJanusRelativeMetricProductFrechet.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem relativeMetricTarget_hasFDerivAt",
            "theorem relativeMetricTarget_fderiv",
            "theorem relativeSquareRoot_hasFDerivAt",
            "theorem relativeSquareRoot_fderiv",
        ),
    ),
    "P0EFTJanusMetricInverseRelativeRootFrechet.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem matrixInverse_hasFDerivAt",
            "theorem matrixInverse_fderiv",
            "theorem relativeMetricTarget_hasFDerivAt",
            "theorem relativeMetricTarget_fderiv",
            "theorem relativeSquareRoot_hasFDerivAt",
            "theorem relativeSquareRoot_fderiv",
        ),
    ),
    "P0EFTJanusExplicitBoundaryDensityLedger.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def nonNullGHYDensity",
            "def nullGeneratorDensity",
            "theorem expansionLogFactor_zero",
            "def nullReparametrizationCountertermDensity",
            "def jointDensity",
            "def worldvolumeDensity",
            "structure PointwiseBoundaryDensityLedger",
            "def gravitationalBoundaryDensityLedger",
            "def totalIntegratedTwoSectorBoundaryAction",
            "theorem totalIntegratedTwoSectorBoundaryAction_exchange",
        ),
    ),
    "P0EFTJanusExplicitBoundaryDensityLocalVariations.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem nonNullGHYExtrinsicCurve_hasDerivAt",
            "theorem nullGeneratorInaffinityCurve_hasDerivAt",
            "theorem jointAngleCurve_hasDerivAt",
            "theorem worldvolumeLocalCurve_hasDerivAt",
            "theorem worldvolumeLocalLagrangianCurve_hasDerivAt",
            "theorem worldvolumeTensionCurve_hasDerivAt",
        ),
    ),
    "P0EFTJanusNonNullGHYFirstVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem constrainedInverseVariation_mul_metric_add",
            "theorem metric_mul_constrainedInverseVariation_add",
            "theorem inverseExtrinsicTraceCurve_hasDerivAt",
            "theorem nonNullGHYFirstVariationCurve_hasDerivAt",
            "theorem firstVariation_eq_fixedGeometry_of_metric_measure_zero",
        ),
    ),
    "P0EFTJanusNonNullGHYMeasureVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem det_one_add_smul_polynomial",
            "theorem inducedMetricDeterminantCurve_hasDerivAt",
            "theorem inducedBoundaryMeasureCurve_hasDerivAt",
            "def nonNullGHYIndependentMetricFirstJetCurve",
            "theorem nonNullGHYIndependentMetricFirstJetCurve_hasDerivAt",
        ),
    ),
    "P0EFTJanusNonNullGHYExactInverseCurve.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem matrixInverse_hasFDerivAt",
            "theorem eventually_inducedMetricCurve_isUnit",
            "theorem eventually_exactInducedInverseCurve_inverseWitness",
            "theorem exactInducedInverseCurve_hasDerivAt",
            "theorem nonNullGHYExactInverseCurve_hasDerivAt",
        ),
    ),
    "P0EFTJanusNonNullGHYExtrinsicTraceCurve.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem secondFundamentalFormCurve_hasDerivAt",
            "def extrinsicTraceDerivative",
            "theorem exactExtrinsicTraceCurve_hasDerivAt",
            "theorem nonNullGHYExtrinsicTraceCurve_hasDerivAt",
            "theorem affineNormalMetricJet_normal_hasDerivAt",
            "theorem eventually_exactInverseWitness",
        ),
    ),
    "P0EFTJanusGaussianNormalEHGHYCancellation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem gaussianInverse_mul_gaussianMetric",
            "theorem gaussianMetric_mul_gaussianInverse",
            "theorem palatiniNormalVector_eq",
            "theorem stokesContractedPalatini_plus_sign",
            "theorem stokesContractedPalatini_minus_sign",
            "theorem einsteinHilbertDirichletBoundaryFlux_eq",
            "theorem einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero",
            "theorem exactGHYCurve_hasDerivative_neg_einsteinHilbertFlux",
        ),
    ),
    "P0EFTJanusGaussianNormalEmbeddedHypersurface.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure GaussianAffineData",
            "theorem hypersurfaceEmbedding_injective",
            "theorem point_mem_hypersurface_range_iff",
            "theorem surfaceInverse_mul_metric",
            "theorem spacetimeMetric_normalLine_hasDerivAt",
            "theorem leviCivitaChristoffel_lower_symmetric",
            "theorem signedUnitNormal_norm_sq",
            "theorem covariantNormalSecondFundamentalForm_eq",
            "theorem extrinsicTrace_eq",
        ),
    ),
    "P0EFTJanusGaussianNormalIntegratedBoundaryBox.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure CompactTangentBox",
            "theorem tangentBoxSet_volume_lt_top",
            "def tangentBoxIntegral",
            "structure BoxIntervalIntegrable",
            "theorem boxIntervalIntegrable_const",
            "theorem localEH_add_GHY_density_eq_zero",
            "theorem einsteinHilbertFluxDensity_boxIntervalIntegrable",
            "theorem exactGHYDerivativeDensity_boxIntervalIntegrable",
            "theorem integrated_EH_add_exact_GHY_eq_zero",
            "theorem integrated_cancellation_orientation_cases",
            "theorem integratedTwoSectorBoundaryLedger_eq_zero",
            "theorem oppositeOrientedTwoSectorBoundaryLedger_eq_zero",
        ),
    ),
    "P0EFTJanusNullExpansionCountertermVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem expansionCountertermFactor_hasDerivAt",
            "theorem varying_expansionLogFactor_eq",
            "theorem declaredNullCountertermExpansionFamily_hasDerivAt",
            "theorem zeroExpansionApproach_tendsto_zero",
            "theorem derivativeCoefficient_zeroExpansionApproach",
            "theorem derivativeCoefficient_unbounded_below_along_zeroExpansionApproach",
        ),
    ),
    "P0EFTJanusNullExpansionCountertermNonDifferentiable.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem zeroExtendedExpansionCountertermFactor_continuous",
            "theorem zeroExpansionSequence_tendsto_zero_from_right",
            "theorem zeroExpansionDifferenceQuotient_eq",
            "theorem zeroExpansionDifferenceQuotient_tendsto_atBot",
            "theorem zeroExtendedExpansionCountertermFactor_not_hasDerivAt_zero",
            "theorem zeroExtendedExpansionCountertermFactor_not_differentiableAt_zero",
        ),
    ),
    "P0EFTJanusNullJointReparametrizationCancellation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure NullGeneratorReparametrizationData",
            "theorem shiftedInaffinity_sub_inaffinity",
            "theorem area_mul_sigma_hasDerivAt",
            "theorem localFaceShift_eq_productDerivative",
            "theorem exactEndpointLedger_faceTransgression",
            "theorem exactEndpointLedger_totalShift_zero",
        ),
    ),
    "P0EFTJanusLLBraneAuxiliaryActionVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure LLBraneAuxiliaryPointData",
            "theorem gaugeInvariantF2_eq_minor",
            "def toWorldvolumePointData",
            "theorem llAuxiliaryDensityGammaCurve_hasDerivAt",
            "theorem llAuxiliaryDensityPhiCurve_hasDerivAt",
            "theorem llAuxiliaryDensityFluxCurve_hasDerivAt",
            "theorem auxiliaryStress_symmetric",
            "theorem gammaStationary_iff_auxiliaryStress_eq_zero",
            "theorem phiStationary_iff_measure_constraint",
            "theorem lightlikeBranch_inducedMetric_has_nonzero_kernel",
        ),
    ),
    "P0EFTJanusLLBraneCompositeMeasureVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def affineAuxiliaryFields",
            "theorem affineAuxiliaryFields_coordinate_curve_hasDerivAt",
            "def compositeMeasure",
            "theorem compositeMeasure_curve_hasDerivAt",
            "theorem compositeMeasure_coordinateReparametrized",
            "theorem compositeMeasure_coordinateVolume_compensated",
            "theorem identityAuxiliaryJet_measure_nonzero",
            "theorem identityAuxiliaryJet_measure_has_nonzero_variation",
        ),
    ),
    "P0EFTJanusLLBraneCompositeMeasureFrechet.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def FrobeniusHasFDerivAt",
            "def entryCovector",
            "def compositeMeasureFrechetDerivative",
            "theorem compositeMeasureFrechetDerivative_apply",
            "theorem compositeMeasure_hasFDerivAt",
        ),
    ),
    "P0EFTJanusExplicitBulkBoundaryCancellation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem ghyBoundaryAction_hasFDerivAt_zero",
            "theorem matched_sector_firstVariation_eq_interior",
            "theorem matched_localTwoSectorAction_fderiv",
            "theorem matched_stationary_iff_interiorEuler_zero",
            "theorem mismatched_plus_coefficient_leaves_nonzero_flux",
        ),
    ),
    "P0EFTJanusFiniteBoxBulkBoundaryStokes.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem orientedBoundaryFlux_eq_six_faces",
            "theorem sum_forwardDifference",
            "theorem boxSum_forwardDifference_x",
            "theorem boxSum_forwardDifference_y",
            "theorem boxSum_forwardDifference_z",
            "theorem bulkDivergence_eq_orientedBoundaryFlux",
            "theorem matchedBulkBoundaryFirstVariation_eq_zero",
            "theorem twoSectorBulkBoundaryFirstVariation_eq_zero",
            "theorem twoSectorBulkBoundaryFirstVariation_sectorExchange",
            "theorem bulkDivergence_fluxLine",
            "theorem orientedBoundaryFlux_fluxLine",
            "theorem bulkFluxAction_fluxLine_hasDerivAt",
            "theorem boundaryFluxAction_fluxLine_hasDerivAt",
            "theorem matchedBulkBoundaryAction_fluxLine_hasDerivAt",
        ),
    ),
    "P0EFTJanusFiniteGramInducedMetricFrechetBridge.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem inducedGramMetric_pos_of_admissible",
            "theorem inducedGramMetric_hasFDerivAt",
            "theorem inducedGramMetric_second_fderiv",
            "theorem gramCompatibilityMap_hasFDerivAt",
            "theorem gramPulledBackAction_hasFDerivAt",
        ),
    ),
    "P0EFTJanusFiniteJetCompatibilityNaturality.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem finiteJetCompatibilityOperator_hasFDerivAt",
            "theorem finiteJetCompatibilityOperator_source_natural",
            "theorem finiteJetCompatibilityLinearization_source_intertwines",
            "theorem finiteJetCompatibilityOperator_ambient_invariant",
            "theorem finiteJetCompatibilityLinearization_ambient_intertwines",
            "theorem ambientInfinitesimalDirection_mem_ker",
        ),
    ),
    "P0EFTJanusFiniteJetCompatibilityPrincipalSymbol.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def finiteJetCompatibilityPrincipalSymbol",
            "theorem finiteJetCompatibilityPrincipalSymbol_apply",
            "theorem principalSymbol_eq_zero_iff_range_orthogonal",
            "theorem principalSymbol_injective_of_surjective",
        ),
    ),
    "P0EFTJanusLorentzianGramCompatibilityFrechet.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem lorentzPair_coordinate_formula",
            "theorem lorentzPair_left_nondegenerate",
            "theorem lorentzGramCompatibilityOperator_hasFDerivAt",
            "theorem lorentzGramCompatibilityOperator_source_natural",
            "theorem lorentzGramCompatibilityOperator_ambient_invariant",
            "theorem lorentzGramLinearization_kernel_exact_of_equiv",
            "theorem lorentzGramPrincipalSymbol_eq_zero_iff_range_etaOrthogonal",
            "theorem lorentzGramPrincipalSymbol_injective_of_surjective",
        ),
    ),
    "P0EFTJanusSaintVenantCompatibilitySymbolExactness.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def lorentzGramCanonicalSymbol",
            "def saintVenantSymbol",
            "theorem saintVenantSymbol_lorentzGramCanonicalSymbol_eq_zero",
            "theorem lorentzGramCanonicalSymbol_injective",
            "theorem tensor_eq_strainSymbol_reconstructed_of_symmetric_of_kernel",
            "theorem canonical_lorentzGram_saintVenant_symbol_sequence_exact",
        ),
    ),
    "P0EFTJanusReducedTwoMetricActionDiagonalNoetherAudit.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem reducedTwoMetricAction_diagonalTranslation_hasDerivAt",
            "theorem additivelyDiagonalInvariant_iff_coefficients",
            "theorem positive_interaction_not_additivelyDiagonalInvariant",
        ),
    ),
    "P0EFTJanusCandidateMinisuperspaceLapseConstraint.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem spectralPotential_on_flrwDiagonalSpectrum",
            "theorem reciprocal_spectral_interaction_is_lapse_linear",
            "theorem plus_lapse_variation_is_primary_constraint_precursor",
            "theorem minus_lapse_variation_is_primary_constraint_precursor",
            "theorem mixed_lapse_second_variation_vanishes",
            "theorem lapse_linearity_alone_does_not_supply_secondary_constraint",
        ),
    ),
    "P0EFTJanusReducedFLRWSecondaryConstraint.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem plusConstraint_phaseLine_hasDerivAt",
            "theorem minusConstraint_phaseLine_hasDerivAt",
            "theorem primary_poisson_bracket_factorization",
            "theorem secondary_constraint_of_primary_preservation",
            "theorem secondaryConstraint_phaseLine_hasDerivAt",
            "theorem witness_is_regular_dynamical_branch",
            "theorem witness_is_outside_pt_exchange_flat_family",
            "theorem witness_constraint_differentials_independent",
            "theorem witness_secondary_preservation_fixes_lapse_ratio",
        ),
    ),
    "P0EFTJanusReducedFLRWLegendreBridge.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem reducedCandidateLagrangian_plusVelocity_hasDerivAt",
            "theorem reducedCandidateLagrangian_minusVelocity_hasDerivAt",
            "theorem plusMomentum_after_velocityFromMomentum",
            "theorem minusMomentum_after_velocityFromMomentum",
            "theorem flrw_commonInteraction_eq_reducedInteractionLagrangian",
            "theorem reducedLegendreTransform_eq_lapse_constraints",
        ),
    ),
    "P0EFTJanusPTFlatVacuumFLRWConstraintNoGo.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem ptFlat_plusPotential_factor",
            "theorem ptFlat_minusPotential_factor",
            "theorem simultaneous_primary_constraints_force_symmetric_vacuum",
            "theorem primary_differentials_dependent_on_symmetric_vacuum",
            "theorem ptFlat_vacuum_FLRW_constraint_noGo",
        ),
    ),
    "P0EFTJanusMatterCurvatureFLRWConstraintBranch.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure MatterCurvatureParameters",
            "theorem extendedPlusConstraint_phaseLine_hasDerivAt",
            "theorem extendedMinusConstraint_phaseLine_hasDerivAt",
            "theorem extended_primary_poisson_eq_secondary",
            "theorem witness_lies_on_both_primary_constraints",
            "theorem witness_lies_on_dynamical_secondary_branch",
            "theorem witness_primary_covectors_independent",
            "theorem witness_constraintJacobianMinor_exact",
            "theorem witness_constraintJacobianMinor_nonzero",
            "theorem witness_secondary_preservation_relation",
            "theorem witness_secondary_preservation_fixes_lapse_ratio",
        ),
    ),
    "P0EFTJanusDustFLRWConstrainedStability.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem constrainedTangent_iff_multiple",
            "theorem tangentGenerator_is_constrained",
            "theorem fixedLapseHamiltonian_tangentAffineLine_hasDerivAt",
            "theorem fixedLapseHamiltonian_tangentGenerator_secondVariation",
            "theorem exactConstraintCurve_has_tangentGenerator",
            "theorem exactConstraintCurve_lies_on_constraints",
            "theorem fixedLapseHamiltonian_exactConstraintCurve_hasDerivAt",
            "theorem fixedLapseHamiltonian_exactConstraintCurve_secondVariation",
        ),
    ),
    "P0EFTJanusCandidateSourceModeDecomposition.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem candidateA_source_coupling_mode_decomposition",
            "theorem candidateA_relative_mode_unsourced_iff_equal_sources",
            "theorem candidateA_single_sheet_source_excites_relative_mode",
            "theorem candidateA_opposite_pt_sources_are_pure_relative",
        ),
    ),
    "P0EFTJanusCandidateSchemeFreedomAudit.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure CandidateASchemeParameters",
            "theorem candidateA_commonInteraction_eq_scaled_ptFlatEnergy",
            "theorem candidateA_flat_compatible",
            "theorem candidateA_pt_paired_anomaly_proxy_cancels",
            "theorem finite_even_scheme_freedom_witness",
            "theorem overall_normalization_freedom_witness",
            "theorem anomaly_cancellation_alone_cannot_fix_candidateA_scheme",
        ),
    ),
    "P0EFTJanusFiniteModeHeatKernelAnomalyRegulator.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure FiniteChiralSpectrum",
            "abbrev RegulatorTime",
            "def regulatedChiralTrace",
            "theorem regulatedChiralTrace_ptPartner",
            "theorem pairedRegulatedChiralTrace_eq_zero",
            "theorem pairedRegulatedEvenHeatTrace_eq_two_mul",
            "theorem oneZeroMode_regulated_witness",
        ),
    ),
    "P0EFTJanusPairedHeatKernelCutoffLimit.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure CountableChiralSpectrum",
            "theorem pairedCutoffChiralTrace_tendsto_zero",
            "theorem cutoffChiralTrace_tendsto_infiniteTrace",
            "theorem pairedInfiniteChiralTrace_eq_zero",
            "theorem pairedCutoffChiralTrace_tendsto_infinitePair",
        ),
    ),
    "P0EFTJanusCircleDiracHeatTraceCancellation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure CircleTwist",
            "abbrev HeatTime",
            "def circleDiracAction",
            "theorem pt_eigenvalueSq_eq_positive",
            "theorem heatWeight_positive_summable",
            "theorem cutoffEvenHeatTrace_tendsto",
            "theorem cutoffChiralHeatTrace_tendsto",
            "theorem pairedRegulatedChiralTrace_eq_zero",
            "theorem cutoffChiralHeatTrace_positive_add_pt_eq_zero",
        ),
    ),
    "P0EFTJanusCircleUnboundedDiracDomain.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def circleDiracDomain",
            "def circleUnboundedDirac",
            "theorem circleFourierBasis_mem_domain",
            "theorem circleDiracDomain_dense",
            "theorem circleUnboundedDirac_isFormalAdjoint_self",
            "theorem mem_circleUnboundedDirac_graph_iff",
            "theorem circleUnboundedDirac_isClosed",
            "theorem circleUnboundedDirac_not_uniformly_bounded",
            "theorem circleUnboundedDirac_isSelfAdjoint",
        ),
    ),
    "P0EFTJanusCircleDiracHeatFunctionalBridge.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem circleUnboundedDirac_basis_image_mem_domain",
            "theorem circleUnboundedDirac_squared_on_basis",
            "theorem circleOperatorHeatWeight_eq_heatWeight",
            "theorem circleSpectralHeatMode_diagonal",
            "theorem circleOperatorHeatWeight_summable",
            "theorem circleOperatorEvenHeatTrace_eq_evenHeatTrace",
            "theorem circleOperatorChiralHeatTrace_eq_regulatedChiralTrace",
            "theorem circleOperatorCutoffChiralHeatTrace_positive_add_pt_eq_zero",
            "theorem circleOperatorChiralHeatTrace_positive_add_pt_eq_zero",
        ),
    ),
    "P0EFTJanusCircleHeatSemigroupOperator.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem circleHeatMultiplier_norm_le_one",
            "noncomputable def circleHeatSemigroup",
            "theorem circleHeatSemigroup_apply",
            "theorem circleHeatSemigroup_opNorm_le_one",
            "theorem circleHeatSemigroup_on_basis",
            "theorem circleHeatSemigroup_zero",
            "theorem circleHeatSemigroup_add",
            "theorem circleHeatMultiplier_of_heatTime_eq_operatorHeatWeight",
            "theorem circleHeatSemigroupDiagonalTrace_eq_operatorEvenHeatTrace",
            "theorem circleHeatSemigroupChiralDiagonalTrace_eq_operatorChiralHeatTrace",
            "theorem circleHeatSemigroupChiralDiagonalTrace_positive_add_pt_eq_zero",
        ),
    ),
    "P0EFTJanusCircleHeatSemigroupStrongContinuity.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem circleHeatMultiplier_continuous",
            "theorem circleHeatCoordinateDifferenceSquare_tendsto",
            "theorem circleHeatCoordinateBound_summable",
            "theorem circleHeatSemigroup_stronglyContinuous",
            "theorem circleHeatSemigroup_tendsto_zero",
            "theorem circleHeatBasisOrbitReal_hasDerivAt",
            "theorem circleHeatBasisOrbitReal_hasDerivAt_zero",
        ),
    ),
    "P0EFTJanusCircleHeatSemigroupCompactness.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def circleHeatFiniteTruncation",
            "theorem circleHeatFiniteTruncation_isCompact",
            "theorem circleHeatSemigroup_sub_truncation_opNorm_le",
            "theorem circleHeatTailBound_tendsto_zero",
            "theorem circleHeatFiniteTruncation_tendsto_heatSemigroup",
            "theorem circleHeatSemigroup_isCompact",
        ),
    ),
    "P0EFTJanusProgramPD7CircleHeatRegulatorBridge.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem d7_circleEigenvalue_eq_scaled_programP",
            "theorem programP_heatWeight_eq_d7_circleHeatWeight",
            "theorem d7CircleHeatOperator_isCompact",
            "theorem d7SeparatedLevelHeatOperator_isCompact",
            "theorem d7SeparatedLevelHeatOperator_on_basis",
            "theorem circle_compactness_and_z4_determinant_close_physical_regulator",
            "theorem circle_regulator_and_unconditional_sphere_small_time",
            "theorem circle_compactness_and_quadratic_remainder_close_d7_regulator",
        ),
    ),
    "P0EFTJanusCandidateSignedChargeNewtonianBridge.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def candidateAPTChargedMatter",
            "theorem candidateA_pt_matter_hessian_positive",
            "theorem candidateA_mediator_quadratic_positive",
            "theorem candidateA_mediator_energy_at_stationary",
            "theorem candidateA_signed_mediator_cross_term",
            "theorem candidateA_positive_kinetic_full_janus_sign_matrix",
        ),
    ),
    "P0EFTJanusLorentzBoostRootOrbit.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem rootOrbit_square_eq_metricRelative",
            "theorem rootOrbit_nonDiagonal",
            "theorem minusMetric_symmetric",
            "theorem minusMetric_det",
            "theorem rootOrbit_hasDerivAt",
            "theorem relativeTarget_hasDerivAt",
            "theorem rootOrbit_derivative_sylvester",
            "theorem lorentzBoostRootOrbit_gate",
        ),
    ),
    "P0EFTJanusLorentzJordanIndependentMetricRoot.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem minusMetric_symmetric",
            "theorem minusMetric_det",
            "theorem metricRelative_eq_jordanRelative",
            "theorem jordanRoot_square_eq_metricRelative",
            "theorem jordanRelative_displacement_square",
            "theorem jordanRelative_not_realDiagonalizable",
            "theorem jordanRoot_hasDerivAt",
            "theorem jordanRoot_derivative_sylvester",
            "theorem lorentzJordanIndependentMetricRoot_gate",
        ),
    ),
    "P0EFTJanusLorentzPrincipalRootChart2D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def RootChartCondition",
            "theorem relativeMatrix_is_metric_relative",
            "theorem minusMetric_lorentzByDet",
            "theorem chartRoot_square_eq_metricRelative",
            "theorem chartRoot_det_pos",
            "theorem chartRoot_trace",
            "theorem chartRoot_continuousAt",
            "theorem lorentzPrincipalRootChart2D_gate",
        ),
    ),
    "P0EFTJanusLorentzRootSylvesterChart2D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def sylvesterLinear",
            "theorem equalDiagonalSylvesterInverse_right",
            "theorem equalDiagonal_sylvester_bijective",
            "theorem chartSylvesterInverse_right",
            "theorem chart_sylvester_bijective",
            "theorem squareCurve_derivative_sylvester",
            "theorem chartRoot_directionalDerivative_eq_sylvesterInverse",
            "theorem explicitChartRoot_directionalDerivative_eq_sylvesterInverse",
            "theorem lorentzRootSylvesterChart2D_gate",
        ),
    ),
    "P0EFTJanusLorentzLocalRootBranch4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure SylvesterEquivWitness",
            "theorem matrixSquare_hasStrictFDerivAt",
            "def localRootBranch",
            "theorem eventually_matrixSquare_localRootBranch",
            "theorem localRootBranch_hasFDerivAt",
            "def identitySylvesterWitness",
            "theorem lorentzLocalRootBranch4D_gate",
        ),
    ),
    "P0EFTJanusCircleHeatGeneratorDomain.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def circleDiracSquaredDomain",
            "def circleUnboundedDiracSquared",
            "def circleDiracIteratedDomain",
            "theorem circleDiracSquaredDomain_eq_iteratedDomain",
            "def circleHeatDifferenceQuotient",
            "theorem circleHeatDifferenceQuotient_tendsto_of_mem_squaredDomain",
            "def circleHeatGeneratorDomain",
            "theorem circleHeatGeneratorDomain_eq_circleDiracSquaredDomain",
            "theorem circleHeatGenerator_eq_neg_diracSquared",
        ),
    ),
    "P0EFTJanusCircleHeatNuclearTraceClass.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def circleHeatRankOne",
            "theorem circleHeatRankOne_opNorm_le",
            "theorem circleHeatRankOne_norm_summable",
            "def circleHeatNuclearSum",
            "theorem circleHeatNuclearSum_eq_semigroup",
            "structure CircleHeatNuclearCertificate",
            "def circleHeatNuclearCertificate",
            "def circleHeatNuclearTrace",
            "theorem circleHeatNuclearTrace_eq_operatorEvenHeatTrace",
            "theorem circleHeatNuclearNormSum_le_trace",
        ),
    ),
    "P0EFTJanusLorentzRootRegularTube4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def localTargetLift",
            "theorem eventually_localTargetLift_square",
            "theorem localTargetLift_hasFDerivAt",
            "theorem continuousRootLift_eventuallyEq_localTargetLift",
            "theorem continuousRootLift_hasFDerivAt",
            "theorem continuousRootLift_derivative_sylvester",
            "theorem relativeMetricRoot_hasFDerivAt_of_continuous",
            "theorem lorentzRootRegularTube4D_gate",
        ),
    ),
    "P0EFTJanusMinkowskiRelativeRootBranch4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def minkowskiMetricPair",
            "def minkowskiRelativeRootBranch",
            "theorem minkowskiRelativeRootBranch_hasFDerivAt",
            "theorem eventually_minkowskiRelativeRootBranch_square",
            "theorem minkowskiRelativeRootBranch_fderiv_apply",
            "theorem minkowski_relative_root_local_closure",
        ),
    ),
    "P0EFTJanusMinkowskiRelativeRootOpenDomain4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def identityRootTarget",
            "def minkowskiRelativeRootOpenDomain",
            "theorem minkowskiRelativeRootOpenDomain_isOpen",
            "theorem minkowskiMetricPair_mem_openDomain",
            "theorem minkowskiRelativeRootBranch_square_on_openDomain",
            "theorem minkowskiRelativeRootBranch_continuousOn_openDomain",
            "theorem root_unique_in_identityChart",
            "theorem minkowski_relative_root_open_domain_closure",
        ),
    ),
    "P0EFTJanusMinkowskiInteractionDensityVariation4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure SymmetricMetricPairVariation4",
            "theorem minkowskiPlusVolume_hasFDerivAt",
            "theorem minkowskiRoot_hasFDerivAt",
            "theorem minkowskiRootPotential_hasFDerivAt",
            "theorem minkowskiCandidateAInteractionDensity_hasFDerivAt",
            "theorem minkowskiCandidateAInteractionDensityDerivative_apply_explicit",
            "theorem minkowskiCandidateAInteractionDensity_curve_hasDerivAt",
            "theorem eventually_minkowskiMetricPairCurve_root_square",
        ),
    ),
    "P0EFTJanusMinkowskiInteractionDensityOpenDomain4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem identityRootSource_approximates",
            "theorem sylvesterMap_isUnit_on_identityRootSource",
            "theorem minkowskiRelativeRootChart_hasFDerivAt_on_openDomain",
            "theorem minkowskiRelativeRootBranch_differentiableAt_on_openDomain",
            "theorem minkowskiPlusVolume_hasFDerivAt_on_openDomain",
            "theorem minkowskiRootPotential_hasFDerivAt_on_openDomain",
            "theorem minkowskiCandidateAInteractionDensity_hasFDerivAt_on_openDomain",
            "theorem ptPairedRootOpenDomain_isOpen",
            "theorem exchangedCandidateAInteractionDensity_hasFDerivAt",
            "theorem ptPairedCandidateAInteractionDensity_hasFDerivAt",
            "theorem ptPairedCandidateAInteractionDensity_exchange",
        ),
    ),
    "P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure OpenDomainMetricFieldVariation",
            "def integratedCandidateAFunctional",
            "def pointwiseCandidateAFirstVariation",
            "structure DominatedInteractionIntegralContract",
            "theorem integratedCandidateAActionCurve_integrable_and_hasDerivAt",
            "theorem integratedCandidateAActionCurve_exchange",
            "structure MeasuredPTBase",
            "theorem integratedCandidateAFunctional_measuredPTExchange",
            "theorem integratedCandidateAActionCurve_measuredPT_hasDerivAt",
            "def effectiveD8SpacetimePTHomeomorph",
            "def effectiveD8MeasuredPTBase",
        ),
    ),
    "P0EFTJanusGlobalDiagonalLorentzRoot4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def globalDiagonalLorentzDomain",
            "theorem globalDiagonalLorentzDomain_isOpen",
            "theorem globalDiagonalLorentzDomain_isConnected",
            "theorem lorentzMetricInverse_mul",
            "theorem principalRoot_square",
            "theorem principalRoot_exists_unique",
            "def principalRootSylvesterInverseWitness",
            "theorem principalRoot_contDiffOn",
            "theorem metricProduct_hasFDerivAt",
            "theorem principalRoot_hasFDerivAt",
            "theorem principalRootVariation_eq_sylvester",
        ),
    ),
    "P0EFTJanusMetricCoupledScalarMatterJetVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure ScalarMatterJet",
            "theorem scalarKinetic_line_hasDerivAt",
            "theorem scalarMatterDensity_line_hasDerivAt",
            "theorem scalarMatterDensity_fieldLine_hasDerivAt",
            "theorem scalarMatterDensity_inverseMetricLine_hasDerivAt",
            "theorem scalarMatterDensity_gradientLine_hasDerivAt",
            "theorem scalarMatterDensity_measureLine_hasDerivAt",
            "theorem twoSector_plusFieldLine_hasDerivAt",
            "theorem twoSector_mixed_field_increment_eq_zero",
        ),
    ),
    "P0EFTJanusMetricInducedScalarStressVariation4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def fixedDeterminantSignDomain",
            "theorem fixedDeterminantSignDomain_isOpen",
            "structure FixedSignMetric4",
            "theorem eventually_metricCurve_mem_domain",
            "theorem exactInverseMetricCurve_hasDerivAt",
            "theorem metricMeasureCurve_hasDerivAt",
            "theorem metricInducedScalarDensityCurve_hasDerivAt",
            "def pointwiseScalarStressTensor",
            "theorem pointwiseScalarStressTensor_symmetric",
            "theorem metricInducedScalarDensityFirstVariation_eq_stress_pairing",
            "theorem metricInducedScalarDensityCurve_stress_hasDerivAt",
        ),
    ),
    "P0EFTJanusIntegratedScalarStressVariation4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure ScalarMetricSector4",
            "def integratedScalarAction",
            "def integratedScalarStressVariation",
            "def shiftedFixedSignMetric4",
            "theorem shifted_metricInducedScalarDensityCurve",
            "theorem metricInducedScalarDensityCurve_stress_hasDerivAt_at",
            "def pointwiseScalarStressVariationAt",
            "theorem integratedScalarAction_stress_hasDerivAt",
            "theorem integratedScalarAction_stress_hasDerivAt_of_deriv_le",
            "structure TwoScalarMetricSectors4",
            "theorem exchangeTwoScalarMetricSectors4_involutive",
            "theorem integratedTwoSectorScalarAction_exchange",
            "theorem integratedTwoSectorScalarStressVariation_exchange",
            "theorem integratedTwoSectorScalarAction_stress_hasDerivAt",
        ),
    ),
    "P0EFTJanusHolonomicScalarFieldVariation4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def coordinateGradient",
            "def holonomicScalarJet",
            "def scalarFieldLine",
            "theorem fderiv_scalarFieldLine",
            "theorem holonomicScalarJet_scalarFieldLine",
            "def holonomicScalarDensityCurve",
            "theorem holonomicScalarDensityCurve_hasDerivAt",
            "structure HolonomicScalarSector4",
            "def integratedHolonomicScalarAction",
            "def integratedHolonomicScalarFirstVariation",
            "theorem integratedHolonomicScalarAction_hasDerivAt",
        ),
    ),
    "P0EFTJanusHolonomicMetricScalarVariation4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def holonomicMetricScalarDensityCurve",
            "def holonomicMetricScalarDensityFirstVariation",
            "theorem holonomicMetricScalarDensityCurve_hasDerivAt",
            "theorem holonomicMetricScalarDensityFirstVariation_split",
        ),
    ),
    "P0EFTJanusIntegratedHolonomicMetricScalarVariation4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure IntegratedHolonomicMetricScalarSector4",
            "def integratedHolonomicMetricScalarAction",
            "def integratedHolonomicMetricScalarFirstVariation",
            "theorem pointwiseHolonomicMetricScalarDensity_hasDerivAt",
            "theorem integratedHolonomicMetricScalarAction_hasDerivAt",
        ),
    ),
    "P0EFTJanusFlatHolonomicScalarEuler4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def raisedCoordinateGradient",
            "def coordinateDivergence",
            "def scalarBoundaryFlux",
            "def flatScalarEulerOperator",
            "theorem coordinateDivergence_scalarBoundaryFlux",
            "theorem holonomicScalarDensityFirstVariation_euler_decomposition",
            "def ScalarFluxVanishes",
        ),
    ),
    "P0EFTJanusIntegratedFlatScalarEuler4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure FlatScalarEulerSector4",
            "def integratedFlatScalarFirstVariation",
            "def integratedFlatScalarFlux",
            "def integratedFlatScalarEulerPairing",
            "def IntegratedScalarFluxVanishes",
            "theorem pointwise_flatScalarEuler_decomposition",
            "theorem integratedFlatScalarFirstVariation_eq_eulerPairing",
            "theorem integratedHolonomicScalarAction_euler_hasDerivAt",
        ),
    ),
    "P0EFTJanusFinitePeriodicHolonomicScalarVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem discreteGradient_fieldLine",
            "theorem scalarAction_fieldLine_hasDerivAt",
            "theorem discrete_summation_by_parts",
            "theorem strongEuler_eq_nearestNeighbour",
            "theorem scalarActionFirstVariation_eq_strongEuler_pairing",
            "theorem stationary_iff_strongEuler_eq_zero",
            "theorem twoSectorAction_fieldLines_hasDerivAt",
            "theorem twoSector_mixed_increment_eq_zero",
        ),
    ),
    "P0EFTJanusFiniteMetricHolonomicScalarVariation.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem metricKineticWeight_line_hasDerivAt",
            "theorem metricMassWeight_line_hasDerivAt",
            "theorem metricHolonomicAction_line_hasDerivAt",
            "theorem metricHolonomicFirstVariation_fixedMetric",
            "theorem fixedMetric_firstVariation_eq_strongEuler_pairing",
            "theorem fixedMetric_stationary_iff_strongEuler_eq_zero",
            "theorem metricHolonomicAction_metricLine_hasDerivAt",
        ),
    ),
    "P0EFTJanusFiniteMetricHolonomicReindexingCovariance.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def transportShift",
            "def transportField",
            "theorem discreteGradient_transport",
            "theorem metricHolonomicAction_transport",
            "theorem metricHolonomicFirstVariation_transport",
            "theorem strongEuler_transport",
            "theorem fixedMetric_stationary_transport_iff",
            "theorem finiteMetricHolonomicReindexingCovariance_gate",
        ),
    ),
    "P0EFTJanusGlobalFieldConfiguration4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def IsLorentzianMatrix4",
            "structure LorentzMetricPoint4",
            "structure IndependentFields",
            "theorem IndependentFields.replacePlusMetric_minusMetric",
            "theorem IndependentFields.replaceMinusMetric_plusMetric",
            "theorem independentPTExchange_involutive",
            "structure InducedFields",
            "structure FieldInduction",
            "theorem induce_plusInverse_exact",
            "structure FunctionalSpaces",
            "structure BoundaryConditions",
            "structure PTCompatibleContracts",
            "def InductionPTCovariant",
            "theorem realize_pt_covariant",
            "structure GlobalConfiguration",
            "theorem globalConfigurationPTExchange_involutive",
        ),
    ),
    "P0EFTJanusMappingTorusGlobalFieldBridge4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def effectiveSpacetimePT",
            "def effectiveThroatPT",
            "theorem effectiveThroatEmbedding_pt_equivariant",
            "theorem effectiveThroatEmbedding_transform_fixed",
            "def effectiveIndependentPTData",
            "theorem independentPTExchange_preserves_effective_throat",
            "theorem effective_mapping_torus_field_base_closure",
        ),
    ),
    "P0EFTJanusMappingTorusFlatFieldBranch4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def minkowskiLorentzMetricPoint4",
            "def flatDiagonalIndependentFields",
            "def flatDiagonalInducedFields",
            "theorem flatDiagonal_relativeRoot_square",
            "theorem flatDiagonalIndependentFields_pt_fixed",
            "theorem effective_flat_diagonal_branch_nonempty",
        ),
    ),
    "P0EFTJanusMappingTorusContinuousFieldSpaces4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def ContinuousLLPointField",
            "def IndependentFieldsContinuous",
            "def InducedFieldsContinuous",
            "theorem flatDiagonalIndependentFields_continuous",
            "theorem flatDiagonalInducedFields_continuous",
            "structure ContinuousEffectiveConfiguration",
            "def flatContinuousEffectiveConfiguration",
            "theorem continuous_effective_configuration_nonempty",
        ),
    ),
    "P0EFTJanusMappingTorusSmoothDeckInvariantFields4D.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure SmoothDeckInvariantField",
            "def constantField",
            "def descend",
            "theorem continuous_descend",
            "theorem descend_injective",
            "structure SmoothIndependentCoefficientConfiguration",
            "def flatSmoothConfiguration",
            "theorem smooth_deck_invariant_field_gate",
        ),
    ),
    "P0EFTJanusArbitraryFrequencySaintVenantExactness.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem strainSymbol_injective",
            "theorem saintVenantSymbol_eq_zero_iff_exists_strain",
            "theorem range_strainSymbol_eq_symmetric_saintVenant_kernel",
            "theorem lorentzGramSymbol_injective",
            "theorem range_lorentzGramSymbol_eq_symmetric_saintVenant_kernel",
            "theorem arbitrary_frequency_saintVenant_symbol_sequence_exact",
        ),
    ),
    "P0EFTJanusFiniteFourierSaintVenantExactness.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem coefficientSupport_finite",
            "theorem finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero",
            "theorem finiteFourierLorentzGram_reconstructed_eq",
            "theorem finiteFourierLorentzGram_injective",
            "theorem finiteFourierSaintVenant_eq_zero_iff_exists_potential",
            "theorem range_finiteFourierLorentzGram_eq_symmetric_saintVenant_kernel",
            "theorem finite_fourier_saintVenant_sequence_exact",
            "theorem finite_fourier_saintVenant_exactness_gate",
        ),
    ),
    "P0EFTJanusFiniteFourierZeroModeCohomology.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def zeroModeResidual",
            "theorem zeroModeResidual_supported",
            "theorem finiteFourier_zeroMode_decomposition",
            "theorem finiteFourier_zeroMode_decomposition_unique",
            "theorem compatible_iff_existsUnique_zeroMode_decomposition",
            "theorem zeroModeResidual_eq_zero_iff_exists_normalized_potential",
            "theorem finite_fourier_zeroMode_cohomology_gate",
        ),
    ),
    "P0EFTJanusCountableFourierSaintVenantExactness.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def zeroModeResidual",
            "theorem countable_zeroMode_decomposition",
            "theorem compatible_zeroModeFree_iff_exists_normalizedPotential",
            "theorem axialReconstructedPotential_squareSummable",
            "theorem zeroModeResidual_squareSummable",
            "theorem countable_fourier_saintVenant_exactness_gate",
        ),
    ),
    "P0EFTJanusLatticeFourierSaintVenantExactness.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "theorem exists_dominant_lattice_pivot",
            "theorem one_le_abs_latticePivot",
            "theorem lattice_zeroMode_decomposition",
            "theorem dominantPivot_inverse_sq_le",
            "theorem latticeReconstructedPotential_sq_le_finiteSum",
            "theorem latticeReconstructedPotential_squareSummable",
            "theorem latticeReconstructedPotential_weightedSquareSummable",
            "theorem lattice_fourier_saintVenant_exactness_gate",
        ),
    ),
    "P0EFTJanusWeightedL2LatticeSaintVenantExactness.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def weightedReconstruction",
            "theorem weightedReconstruction_opNorm_le",
            "def weightedLorentzGramDomain",
            "noncomputable def weightedLorentzGramLinearMap",
            "def CompatibleZeroFreeMetricSubspace",
            "theorem weightedLorentzGram_range_eq_compatibleZeroFree",
            "theorem weightedLorentzGram_range_isClosed",
            "theorem compatible_metric_hilbert_decomposition",
            "theorem weighted_l2_lattice_saintVenant_exactness_gate",
        ),
    ),
    "P0EFTJanusShiftedSobolevLatticeLorentzGram.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def rawLorentzGramFiberCLM",
            "def symbolGraphScale",
            "theorem normalizedLorentzGramFiber_norm_le",
            "def symbolShiftedSourceWeight",
            "def shiftedSobolevLorentzGram",
            "theorem shiftedSobolevLorentzGram_opNorm_le",
            "theorem shiftedSobolevLorentzGram_eq_zero_iff",
            "theorem normalizedLorentzGramFibers_encode_eq_weightedMetricCoordinates",
            "theorem shiftedSobolevLorentzGram_encode_eq",
            "theorem shifted_sobolev_lattice_lorentzGram_gate",
        ),
    ),
    "P0EFTJanusShiftedSobolevPullbackHessian.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def targetIdentityHessian",
            "theorem targetIdentityHessian_selfAdjoint_pairing",
            "def shiftedPullbackHessian",
            "theorem shiftedPullbackHessian_pairing",
            "theorem shiftedPullbackHessian_symmetric",
            "theorem shiftedPullbackHessian_nonnegative",
            "theorem shiftedPullbackHessian_apply_eq_zero_iff_zeroModeSupport",
            "theorem shiftedPullbackHessian_positiveDefinite_of_zeroModeFree",
            "theorem shifted_pullback_hessian_gate",
        ),
    ),
    "P0EFTJanusShiftedSobolevPhysicalQuotient.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def potentialZeroModeProjection",
            "theorem potentialZeroModeProjection_opNorm_le",
            "theorem zeroMode_range_isTopCompl_ker",
            "theorem zeroModeProjection_range_eq_symbol_ker",
            "abbrev PhysicalPotentialQuotient",
            "def physicalQuotientEquivZeroFree",
            "theorem pullbackHessian_nondegenerate_on_physical_representatives",
            "theorem shifted_sobolev_physical_quotient_gate",
        ),
    ),
    "P0EFTJanusFiniteSpatialFunctionalPoisson.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "def finitePoisson",
            "theorem finitePoisson_add_left",
            "theorem finitePoisson_scale_left",
            "theorem finitePoisson_antisymmetric",
            "theorem affine_poisson_jacobi",
            "theorem plusFunctional_fieldLine_hasDerivAt",
            "theorem minusFunctional_fieldLine_hasDerivAt",
            "theorem plus_minus_functional_poisson_eq_secondary_sum",
            "theorem local_plus_preservation",
            "theorem local_minus_preservation",
            "theorem secondary_at_site_of_local_primary_preservation",
            "theorem twoSiteWitness_local_constraint_covectors_independent",
            "theorem twoSiteWitness_secondary_preservation_fixes_each_lapse_ratio",
        ),
    ),
    "P0EFTJanusNonlinearCanonicalPoissonJetJacobi.lean": (
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
        (
            "structure SymmetricHessian4",
            "theorem hessianMatrix_symmetric",
            "theorem poisson_antisymmetric",
            "theorem poisson_covectorVector_eq_canonicalPoisson",
            "def bracketDifferential",
            "theorem nonlinear_poisson_secondJet_jacobi",
            "theorem quadraticFunctional_vectorLine_hasDerivAt",
            "theorem quadraticPoisson_vectorLine_hasDerivAt",
            "theorem nonlinearHessianWitness_nonzero",
        ),
    ),
}

PROGRAM_P_D10_BRIDGE_GATES = {
    "P0EFTJanusProgramPD7Z4SpectralAnomalyBridge.lean": (
        "JanusFormal/Branches/FundamentalGeometryD10QuillenAnomaly.lean",
        (
            "theorem program_p_d7_z4_cutoff_converges",
            "theorem program_p_d7_pt_renormalized_logs_agree",
            "theorem program_p_d7_mode_inflow_cancels",
            "structure PhysicalZ4SpectralAnomalyCertificate",
            "def physicalZ4SpectralAnomalyCertificate",
        ),
    ),
}

PROGRAM_P_D10_FINITE_MODE_GATES = {
    "P0EFTJanusFiniteModeFredholmDeterminantLine.lean": (
        "JanusFormal/Branches/FundamentalGeometryD10QuillenAnomaly.lean",
        (
            "theorem cutoffDiracMatrix_holomorphic",
            "theorem cutoffDirac_kernel_and_cokernel_finite",
            "theorem cutoffFredholmIndex_zero",
            "def cutoffDeterminantLineSection",
            "theorem cutoffDeterminantLine_finrank_one",
            "theorem cutoffDirac_pt_covariant",
            "theorem quarter_holonomy_cutoffs_invertible",
        ),
    ),
}

PROGRAM_P_D10_INFINITE_CIRCLE_GATES = {
    "P0EFTJanusCircleHolonomyCommonDomainCompactResolvent.lean": (
        "JanusFormal/Branches/FundamentalGeometryD10QuillenAnomaly.lean",
        (
            "theorem circleDiracDomain_eq_holonomy",
            "theorem circleUnboundedDirac_holonomy_perturbation",
            "theorem complexHolonomyCircleDirac_contDiff",
            "theorem circleDirac_bounded_window_finite",
            "theorem circleShiftIResolvent_mem_domain",
            "theorem circleShiftIResolvent_right_inverse",
            "theorem circleShiftIResolvent_left_inverse",
            "theorem circleShiftIResolvent_compact",
        ),
    ),
    "P0EFTJanusCircleGraphFredholmIndex.lean": (
        "JanusFormal/Branches/FundamentalGeometryD10QuillenAnomaly.lean",
        (
            "def circleGraphDiracCLM",
            "theorem circleGraphDirac_range_eq_zeroRestriction_ker",
            "theorem circleGraphDirac_range_isClosed",
            "theorem circleGraphDirac_fredholm_criterion",
            "theorem circleGraphKernel_finrank_eq_zeroModes",
            "theorem circleGraphCokernel_finrank_eq_zeroModes",
            "theorem circleGraphFredholmIndex_zero",
            "theorem circleGraphDeterminantLine_finrank_one",
            "theorem circleGraphDeterminantSection_injective",
            "theorem circleGraphDeterminantSection_ne_zero",
        ),
    ),
    "P0EFTJanusCircleBoundedTransformSpectralFlow.lean": (
        "JanusFormal/Branches/FundamentalGeometryD10QuillenAnomaly.lean",
        (
            "def circleBoundedTransform",
            "theorem circleBoundedTransform_isSelfAdjoint",
            "theorem circleBoundedTransform_lipschitz",
            "theorem circleBoundedTransform_range_isClosed",
            "theorem circleBoundedTransform_fredholm_criterion",
            "theorem circleBoundedTransformFredholmIndex_zero",
            "theorem circleBoundedTransform_bijective_of_interior",
            "def unitPeriodicZeroModeEquiv",
            "def circleFundamentalCrossing",
            "theorem pt_reverses_fundamental_crossing",
        ),
    ),
    "P0EFTJanusCircleDeterminantLineFamily.lean": (
        "JanusFormal/Branches/FundamentalGeometryD10QuillenAnomaly.lean",
        (
            "def circleBoundedKernelZeroModeEquiv",
            "def circleBoundedCokernelZeroModeEquiv",
            "abbrev CircleBoundedDeterminantLine",
            "def circleDeterminantFourierFrame",
            "theorem circleBoundedDeterminantLine_finrank_one",
            "theorem circleDeterminantFourierFrame_ne_zero",
            "def endpointKernelEquiv",
            "def endpointCokernelEquiv",
            "def circleLargeGaugeDeterminantTransition",
            "theorem circleLargeGaugeDeterminantTransition_bijective",
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

    for filename, (facade_path, declarations) in PROGRAM_P_D10_BRIDGE_GATES.items():
        source = (repo_root / D10_GATE_ROOT / filename).read_text(encoding="utf-8")
        for declaration in declarations:
            if declaration not in source:
                raise AssertionError(f"missing Program P/D10 declaration: {declaration}")
        if re.search(r"\b(?:sorry|admit|axiom)\b", source):
            raise AssertionError(f"proof placeholder found in {filename}")

        facade = facades.setdefault(
            facade_path,
            (repo_root / facade_path).read_text(encoding="utf-8"),
        )
        gate_import = f"Gates.{filename.removesuffix('.lean')}"
        if gate_import not in facade:
            raise AssertionError(f"D10 facade omits {filename}")

        status = "physicalZ4SpectralDeterminantAndModeInflowBridgeProved"
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") < 1:
            raise AssertionError(f"D10 facade omits status: {status}")

    for filename, (facade_path, declarations) in PROGRAM_P_D10_FINITE_MODE_GATES.items():
        source = (repo_root / D10_GATE_ROOT / filename).read_text(encoding="utf-8")
        for declaration in declarations:
            if declaration not in source:
                raise AssertionError(f"missing finite-mode D10 declaration: {declaration}")
        if re.search(r"\b(?:sorry|admit|axiom)\b", source):
            raise AssertionError(f"proof placeholder found in {filename}")

        facade = facades.setdefault(
            facade_path,
            (repo_root / facade_path).read_text(encoding="utf-8"),
        )
        gate_import = f"Gates.{filename.removesuffix('.lean')}"
        if gate_import not in facade:
            raise AssertionError(f"D10 facade omits {filename}")

        status = "finiteModeHolomorphicFredholmDeterminantLineProved"
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") < 1:
            raise AssertionError(f"D10 facade omits status: {status}")

    for filename, (facade_path, declarations) in PROGRAM_P_D10_INFINITE_CIRCLE_GATES.items():
        source = (repo_root / D10_GATE_ROOT / filename).read_text(encoding="utf-8")
        for declaration in declarations:
            if declaration not in source:
                raise AssertionError(f"missing infinite-circle D10 declaration: {declaration}")
        if re.search(r"\b(?:sorry|admit|axiom)\b", source):
            raise AssertionError(f"proof placeholder found in {filename}")

        facade = facades.setdefault(
            facade_path,
            (repo_root / facade_path).read_text(encoding="utf-8"),
        )
        gate_import = f"Gates.{filename.removesuffix('.lean')}"
        if gate_import not in facade:
            raise AssertionError(f"D10 facade omits {filename}")

        status = (
            "circleGraphFredholmIndexZeroDeterminantLineProved"
            if filename == "P0EFTJanusCircleGraphFredholmIndex.lean"
            else "circleBoundedTransformSpectralFlowProved"
            if filename == "P0EFTJanusCircleBoundedTransformSpectralFlow.lean"
            else "circleAlgebraicDeterminantLineFamilyAndEndpointTransitionProved"
            if filename == "P0EFTJanusCircleDeterminantLineFamily.lean"
            else "circleHolonomyCommonDomainCompactResolventProved"
        )
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") < 1:
            raise AssertionError(f"D10 facade omits status: {status}")

    primary_facade = facades[
        "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean"
    ]
    d8_smooth_quotient_import = (
        "Gates.P0EFTJanusMappingTorusSmoothQuotientManifold"
    )
    if primary_facade.count(d8_smooth_quotient_import) != 1:
        raise AssertionError("Program P facade omits the D8 smooth quotient manifold")
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
        "paExplicitReciprocalCrossDensitiesProved",
        "paSpectralCrossDensityFrechetHelmholtzProved",
        "paMatrixSquareRootPointwisePotentialConstructed",
        "paExplicitGravitationalBoundaryLedgerDeclared",
        "paFiniteGramInducedMetricFrechetBridgeProved",
        "pcReducedActionAdditiveNoetherProxyClassified",
        "paMatrixSquaringSylvesterFrechetProved",
        "paPositiveDiagonalSylvesterInverseProved",
        "paCoDiagonalLorentzRootChartConstructed",
        "paCoDiagonalLorentzRootFirstDerivativeProved",
        "paLorentzBoostCoordinateOrbitRootVariationProved",
        "paLorentzJordanIndependentMetricRootProved",
        "paLorentzPrincipalRootChart2DProved",
        "paLorentzRootSylvesterChart2DProved",
        "paConditionalRealMatrixLocalRootBranch4DProved",
        "paConditionalContinuousSylvesterRegularRootTube4DProved",
        "paUnconditionalMinkowskiDiagonalLocalRelativeRootBranch4DProved",
        "paExplicitMinkowskiRelativeRootOpenDomain4DProved",
        "paMinkowskiCandidateAInteractionDensityVariation4DProved",
        "paMinkowskiCandidateAInteractionOpenDomain4DProved",
        "paIntegratedMinkowskiCandidateAInteractionOpenDomain4DProved",
        "paGlobalDiagonalLorentzRoot4DProved",
        "paCoDiagonalInteractionDensityFrechetProved",
        "paDiagonalReparametrizationDensityPullbackNoetherProved",
        "paFourDimensionalDensityLieDerivativeNoetherProved",
        "paLinearizedEinsteinBianchiAndGaugeSymbolProved",
        "paConditionalRelativeMetricRootFrechetBridgeProved",
        "paFixedGeometryBoundarySlotVariationsProved",
        "paNonNullGHYPointwiseFirstJetVariationProved",
        "paNonNullGHYDeterminantMeasureFirstJetProved",
        "paNonNullGHYExactInverseCurveVariationProved",
        "paNonNullGHYExtrinsicTraceCurveVariationProved",
        "paGaussianNormalEHGHYCancellationDerived",
        "paGaussianNormalEmbeddedHypersurfaceLeviCivitaProved",
        "paGaussianNormalIntegratedBoundaryBoxCancellationProved",
        "paPTFlatSpectralInteractionIndefinitenessProved",
        "paCandidateMinisuperspacePrimaryConstraintPrecursorProved",
        "paCandidateSourceModeDecompositionProved",
        "paConditionalMetricInverseRelativeRootFrechetBridgeProved",
        "pcConditionalMatrixDiagonalGaugeNoetherProved",
        "pcExplicitMatrixInteractionFrechetNoetherProved",
        "paMatrixInteractionDensityCovarianceProved",
        "paFiniteFieldLocalFrameGaugeInvarianceProved",
        "paExplicitBulkBoundaryLocalCancellationProved",
        "paFiniteBoxBulkBoundaryStokesProved",
        "pcExplicitCandidatePointwiseEulerHelmholtzProved",
        "paIndependentMetricMatterJetVariationProved",
        "paMetricInducedScalarStressVariation4DProved",
        "paIntegratedTwoSectorScalarStressVariation4DProved",
        "paFlatChartHolonomicScalarFieldVariation4DProved",
        "paFlatChartHolonomicMetricScalarVariation4DProved",
        "paIntegratedHolonomicMetricScalarVariation4DUnderDominatedContractProved",
        "paFlatHolonomicScalarEulerDivergenceDecomposition4DProved",
        "paIntegratedFlatScalarWeakEuler4DUnderFluxConditionProved",
        "paFinitePeriodicHolonomicScalarEulerProved",
        "paFiniteMetricHolonomicScalarVariationProved",
        "paFiniteMetricHolonomicReindexingCovarianceProved",
        "paParametrizedGlobalLorentzianFieldConfiguration4DConstructed",
        "paEffectiveD8MappingTorusFieldBasePTClosure4DProved",
        "paEffectiveD8FlatDiagonalFieldBranch4DProved",
        "paEffectiveD8ContinuousFieldSpacesAndPTMatchedConfiguration4DProved",
        "paMappingTorusSmoothDeckInvariantFields4DProved",
        "paEffectiveD8SmoothQuotientManifoldProved",
        "paFiniteJetCompatibilityNaturalityProved",
        "paFiniteJetCompatibilityPrincipalSymbolKernelProved",
        "paLorentzianGramCompatibilityFrechetProved",
        "paCanonicalLorentzGramSaintVenantSymbolExactnessProved",
        "paArbitraryFrequencyLorentzGramSaintVenantSymbolExactnessProved",
        "paFiniteFourierSaintVenantExactnessProved",
        "paFiniteFourierZeroModeCohomologyProved",
        "paCountableAxialFourierSaintVenantExactnessProved",
        "paCountableLatticeFourierSaintVenantExactnessProved",
        "paWeightedL2LatticeSaintVenantExactnessProved",
        "paShiftedSobolevLatticeLorentzGramProved",
        "paShiftedSobolevPullbackHessianProved",
        "paShiftedSobolevPhysicalQuotientProved",
        "paNullExpansionCountertermVariationProved",
        "paNullExpansionCountertermNonDifferentiableProved",
        "paNullJointReparametrizationCancellationProved",
        "paLLBraneAuxiliaryVariationAndNullKernelProved",
        "paLLBraneCompositeMeasureVariationProved",
        "paLLBraneCompositeMeasureFrechetProved",
        "paReducedFLRWBracketFactorizationFromInputHamiltoniansProved",
        "paFiniteUltralocalPrimaryBracketLiftProved",
        "paNonlinearCanonicalPoissonSecondJetJacobiProved",
        "paReducedFLRWLegendreBridgeProved",
        "paPTFlatVacuumFLRWConstraintNoGoProved",
        "paMatterCurvatureFLRWConstraintBranchProved",
        "paDustFLRWConstrainedSecondVariationAuditProved",
        "paFiniteModeHeatKernelAnomalyRegulatorProved",
        "paCountablePairedHeatKernelCutoffLimitProved",
        "paCircleFourierDiracHeatTraceCancellationProved",
        "paCircleUnboundedDiracSelfAdjointProved",
        "paCircleDiracHeatFunctionalBridgeProved",
        "paCircleHeatSemigroupOperatorProved",
        "paCircleHeatSemigroupStrongContinuityProved",
        "paCircleHeatSemigroupCompactnessProved",
        "paCircleHeatGeneratorDomainEqualsDiracSquaredDomainProved",
        "paCircleHeatNuclearTraceClassProved",
        "paProgramPD7CircleHeatRegulatorBridgeProved",
        "paProgramPD7UnconditionalSphereSmallTimeBridgeProved",
        "paCandidateSignedChargeNewtonianBridgeProved",
        "pbCandidateSchemeFreedomNoGoProved",
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

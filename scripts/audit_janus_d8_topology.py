#!/usr/bin/env python3
"""Integrity checks for the effective D8 mapping-torus quotient gate."""

from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusQuotient.lean"
)
NORMAL_LINE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusNormalLine.lean"
)
PT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusPTInvolution.lean"
)
ORIENTATION_DOUBLE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusOrientationDoubleCover.lean"
)
THROAT_COMPLEMENT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusThroatComplementSides.lean"
)
THROAT_COMPLEMENT_CONNECTED_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusThroatComplementConnected.lean"
)
SMOOTH_ATLAS_FRONTIER_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothAtlasFrontier.lean"
)
SMOOTH_DECK_DESCENT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothQuotient.lean"
)
SMOOTH_QUOTIENT_MANIFOLD_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothQuotientManifold.lean"
)
SMOOTH_PT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothPTInvolution.lean"
)
SMOOTH_THROAT_EMBEDDING_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothThroatEmbedding.lean"
)
IS_SMOOTH_EMBEDDING_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusIsSmoothEmbedding.lean"
)
SMOOTH_NORMAL_VECTOR_BUNDLE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothNormalVectorBundle.lean"
)
GLOBAL_NORMAL_EQUIVALENCE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusGlobalNormalEquivalence.lean"
)
DIFFERENTIAL_NORMAL_TOPOLOGICAL_BUNDLE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle.lean"
)
DIFFERENTIAL_NORMAL_SMOOTH_BUNDLE_EQUIVALENCE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence.lean"
)
DIFFERENTIAL_NORMAL_ZERO_NONZERO_STRATIFICATION_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusDifferentialNormalZeroNonzeroStratification.lean"
)
AMBIENT_TANGENT_ORIENTATION_COCYCLE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusAmbientTangentOrientationCocycle.lean"
)
AMBIENT_TANGENT_QUADRATIC_REDUCTION_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusAmbientTangentQuadraticReduction.lean"
)
AMBIENT_SPIN_PROJECTION_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusAmbientSpinProjection.lean"
)
AMBIENT_SPIN_ORIENTATION_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusAmbientSpinOrientation.lean"
)
AMBIENT_SPIN_ATLAS_OBSTRUCTION_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusAmbientSpinAtlasObstruction.lean"
)
SMOOTH_NORMAL_Z4_ROOT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothNormalZ4RootBundle.lean"
)
NORMAL_ROOT_PT_CONJUGATION_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusNormalRootPTConjugation.lean"
)
NORMAL_PIN_MINUS_PRINCIPAL_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle.lean"
)
NORMAL_PIN_MINUS_ASSOCIATED_ROOTS_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusNormalPinMinusAssociatedRoots.lean"
)
COMPACT_QUOTIENT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusCompactQuotient.lean"
)

FACADE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation.lean"
)

DECLARATIONS = (
    "structure MappingTorusData",
    "theorem vadd_eq_self_iff",
    "theorem mappingTorusMk_isCoveringMap",
    "theorem mappingTorus_has_chartedSpace",
    "theorem equatorialSphereInclusion_injective",
    "theorem continuous_fixedThroatQuotientInclusion",
    "theorem fixedThroatQuotientInclusion_injective",
)

STATUSES = (
    "effectiveTopologicalMappingTorusQuotientConstructed",
    "mappingTorusCoveringAndChartedSpaceProved",
    "fixedThroatQuotientInclusionInjectiveProved",
)

NORMAL_LINE_DECLARATIONS = (
    "abbrev MappingTorusNormalLine",
    "def normalLineProjection",
    "theorem continuous_normalLineProjection",
    "def normalLineZeroSection",
    "theorem continuous_normalLineZeroSection",
    "theorem normalLineProjection_zeroSection",
    "theorem one_loop_normal_flip",
    "theorem two_loops_restore_normal",
    "theorem mapping_torus_normal_line_closure",
)

NORMAL_LINE_STATUSES = (
    "associatedNormalLineOrbitQuotientConstructed",
    "associatedNormalLineProjectionContinuousSurjectiveProved",
    "associatedNormalLineZeroSectionConstructed",
    "associatedNormalLineOneLoopFlipProved",
    "associatedNormalLineTwoLoopRestorationProved",
)

PT_DECLARATIONS = (
    "def mappingTorusTimeReversal",
    "theorem continuous_mappingTorusTimeReversal",
    "theorem mappingTorusTimeReversal_involutive",
    "def reflectedSpherePT",
    "theorem continuous_reflectedSpherePT",
    "theorem reflectedSpherePT_involutive",
    "def fixedThroatPT",
    "theorem continuous_fixedThroatPT",
    "theorem fixedThroatPT_involutive",
    "theorem fixedThroatQuotientInclusion_pt_equivariant",
)

PT_STATUSES = (
    "mappingTorusTimeReversalContinuousProved",
    "mappingTorusTimeReversalInvolutiveProved",
    "fixedThroatQuotientInclusionPTEquivariantProved",
)

ORIENTATION_DOUBLE_DECLARATIONS = (
    "abbrev OrientationDoubleThroat",
    "def orientationDoubleToThroat",
    "theorem orientationDoubleToThroat_isCoveringMap",
    "theorem orientationDouble_fiber_equiv_two",
    "theorem orientationDeck_involutive",
    "theorem orientationDeck_ne_self",
    "def orientationNormalTrivialization",
    "theorem orientationDouble_normal_pullback_closure",
)

ORIENTATION_DOUBLE_STATUSES = (
    "effectiveThroatOrientationDoubleCoveringMapProved",
    "throatOrientationDoubleCoverFiberTwoProved",
    "throatOrientationDeckInvolutionFreeProved",
    "throatNormalPullbackTopologicallyTrivializedProved",
)

THROAT_COMPLEMENT_DECLARATIONS = (
    "theorem positiveSphereSide_isOpen",
    "theorem negativeSphereSide_isOpen",
    "theorem positiveSphereSide_nonempty",
    "theorem negativeSphereSide_nonempty",
    "theorem sphere_complement_eq_two_sides",
    "theorem positive_negative_disjoint",
    "theorem sphereReflection_image_positive",
    "theorem one_vadd_mem_negative_iff",
    "theorem mappingTorusMk_preimage_effectiveThroat",
    "theorem image_positiveCoverSide_eq_effective_complement",
    "theorem image_negativeCoverSide_eq_effective_complement",
    "theorem quotient_images_of_sides_coincide",
    "theorem reflectedSpherePT_mem_effective_complement_iff",
)

THROAT_COMPLEMENT_STATUSES = (
    "equatorialSphereComplementTwoOpenSidesProved",
    "reflectionAndDeckExchangeCoverSidesProved",
    "effectiveThroatComplementOneSidedImageProved",
    "effectiveThroatComplementPTInvariantProved",
)

THROAT_COMPLEMENT_CONNECTED_DECLARATIONS = (
    "theorem positiveSphereSide_isPathConnected",
    "theorem negativeSphereSide_isPathConnected",
    "theorem connectedComponentIn_throat_complement_positivePole",
    "theorem connectedComponentIn_throat_complement_negativePole",
    "theorem positiveCoverSide_isPathConnected",
    "theorem effectiveThroat_complement_isPathConnected",
    "theorem effectiveThroat_complement_isConnected",
)

SMOOTH_ATLAS_FRONTIER_DECLARATIONS = (
    "def unitThreeSphereHomeomorph",
    "instance unitThreeSphereIsManifold",
    "def equatorialTwoSphereHomeomorph",
    "instance equatorialTwoSphereIsManifold",
    "theorem unitThreeSphere_prod_real_isManifold",
    "theorem fixedThroatCover_isManifold",
    "theorem fixedThroatCoverInclusion_isEmbedding",
    "theorem fixedThroatCoverInclusion_contMDiff_zero",
    "theorem fixedThroat_quotient_isTopologicalManifold",
    "theorem fixedThroatQuotientInclusion_contMDiff_zero",
    "theorem reflectedSphere_quotient_isTopologicalManifold",
    "theorem reflectedSphere_projection_isLocalHomeomorph",
    "theorem reflectedSphere_projection_contMDiff_zero",
    "theorem reflectedSphere_projection_topological_atlas_closure",
)

SMOOTH_ATLAS_FRONTIER_STATUSES = (
    "algebraicSphereCoversAnalyticManifoldsProved",
    "throatCoverTopologicalEmbeddingAndC0Proved",
    "effectiveMappingTorusTopologicalManifoldProved",
    "effectiveThroatTopologicalManifoldProved",
    "quotientProjectionLocalHomeomorphAndC0Proved",
)

SMOOTH_DECK_DESCENT_DECLARATIONS = (
    "theorem sphereReflection_contMDiff",
    "theorem reflectedSphereCover_deck_contMDiff",
    "theorem fixedThroatCover_deck_contMDiff",
    "theorem fixedThroatCoverInclusion_contMDiff",
    "theorem localInverseAt_eventuallyEq_vadd",
    "theorem smoothHomeomorph_coordinateChange_mem_groupoid",
)

SMOOTH_QUOTIENT_MANIFOLD_DECLARATIONS = (
    "theorem mappingTorus_isManifold_of_smooth_deck",
    "def mappingTorusLocalSectionPartialDiffeomorph",
    "theorem mappingTorus_projection_isLocalDiffeomorph",
    "def fixedThroatQuotientChartedSpace",
    "def reflectedSphereQuotientChartedSpace",
    "theorem fixedThroatQuotient_isManifold",
    "theorem reflectedSphereQuotient_isManifold",
    "theorem fixedThroat_projection_isLocalDiffeomorph",
    "theorem reflectedSphere_projection_isLocalDiffeomorph",
    "theorem fixedThroatQuotientInclusion_contMDiff",
)

SMOOTH_QUOTIENT_MANIFOLD_STATUSES = (
    "effectiveMappingTorusSmoothQuotientManifoldProved",
    "effectiveThroatSmoothQuotientManifoldProved",
    "quotientProjectionLocalDiffeomorphProved",
    "fixedThroatQuotientInclusionContMDiffProved",
)

SMOOTH_PT_DECLARATIONS = (
    "theorem mappingTorusTimeReversal_contMDiff",
    "theorem reflectedSphereCover_timeReverse_contMDiff",
    "theorem fixedThroatCover_timeReverse_contMDiff",
    "theorem reflectedSpherePT_contMDiff",
    "theorem fixedThroatPT_contMDiff",
    "def reflectedSpherePTDiffeomorph",
    "def fixedThroatPTDiffeomorph",
)

SMOOTH_PT_STATUSES = (
    "mappingTorusTimeReversalContMDiffProved",
    "mappingTorusTimeReversalDiffeomorphConstructed",
)

SMOOTH_THROAT_EMBEDDING_DECLARATIONS = (
    "theorem fixedThroatQuotientInclusion_isClosedEmbedding",
    "theorem fixedThroatQuotientInclusion_isEmbedding",
    "theorem mfderiv_fixedThroatQuotientInclusion_injective",
    "theorem mfderiv_fixedThroatQuotientInclusion_normal_finrank",
    "theorem fixedThroatQuotientInclusion_smoothEmbeddingData",
)

SMOOTH_THROAT_EMBEDDING_STATUSES = (
    "fixedThroatQuotientInclusionIsClosedEmbeddingProved",
    "fixedThroatQuotientDifferentialInjectiveProved",
    "fixedThroatNormalQuotientFinrankOneProved",
)

IS_SMOOTH_EMBEDDING_DECLARATIONS = (
    "theorem standardEquatorInclusion_isImmersionOfComplement",
    "theorem equatorialSphereInclusion_isImmersionOfComplement",
    "theorem fixedThroatCoverInclusion_isImmersionOfComplement",
    "theorem fixedThroatQuotientInclusion_isImmersionOfComplement",
    "theorem fixedThroatQuotientInclusion_isImmersion",
    "theorem fixedThroatQuotientInclusion_isSmoothEmbedding",
    "theorem fixedThroatQuotientInclusion_fullSmoothEmbeddingClosure",
)

IS_SMOOTH_EMBEDDING_STATUSES = (
    "fixedThroatQuotientInclusionIsImmersionOfComplementProved",
    "fixedThroatQuotientInclusionIsSmoothEmbeddingProved",
)

SMOOTH_NORMAL_VECTOR_BUNDLE_DECLARATIONS = (
    "def normalBundleBaseSet",
    "def normalBundleIndexAt",
    "def localTransitionWinding",
    "theorem localTransitionWinding_vadd",
    "def normalSignCLM",
    "def fixedThroatNormalVectorBundleCore",
    "theorem fixedThroatNormalFiber_isVectorBundle",
    "theorem fixedThroatNormalVectorBundleCore_isContMDiff",
    "theorem fixedThroatNormalFiber_isContMDiffVectorBundle",
    "theorem fixedThroatNormalFiber_equiv_differentialNormal",
    "theorem localTransitionWinding_one_loop",
    "theorem one_loop_coordChange_eq_neg_id",
)

SMOOTH_NORMAL_VECTOR_BUNDLE_STATUSES = (
    "fixedThroatNormalVectorBundleConstructed",
    "fixedThroatNormalVectorBundleContMDiffProved",
    "fixedThroatNormalFiberPointwiseDifferentialEquivProved",
    "fixedThroatNormalOneLoopMinusIdentityProved",
)

GLOBAL_NORMAL_EQUIVALENCE_DECLARATIONS = (
    "abbrev DifferentialNormalFiber",
    "theorem differentialNormalRange_isClosed",
    "theorem differentialNormalFiber_finrank",
    "noncomputable def differentialNormalFiberEquiv",
    "theorem differentialNormalFiber_continuousEquiv",
    "theorem differentialNormalFiberEquiv_oneLoop",
    "noncomputable def differentialNormalTotalEquiv",
    "theorem differentialNormalGlobalAlgebraicClosure",
)

DIFFERENTIAL_NORMAL_TOPOLOGICAL_BUNDLE_DECLARATIONS = (
    "def differentialNormalFiberContinuousEquiv",
    "def differentialNormalFiberHomeomorph",
    "def differentialNormalTotalHomeomorph",
    "def differentialNormalLocalTriv",
    "theorem differentialNormalLocalTriv_coordChange_eq",
    "theorem differentialNormalTotalSpaceMk_isInducing",
    "theorem differentialNormalFiber_isVectorBundle",
    "theorem differentialNormalFiber_isContMDiffVectorBundle",
)

DIFFERENTIAL_NORMAL_SMOOTH_BUNDLE_EQUIVALENCE_DECLARATIONS = (
    "def differentialNormalTotalDiffeomorph",
    "theorem differentialNormalTotalDiffeomorph_toHomeomorph",
    "theorem differentialNormalTotalDiffeomorph_base",
    "theorem differentialNormalTotalDiffeomorph_fiber",
    "theorem differentialNormalTotalDiffeomorph_add",
    "theorem differentialNormalTotalDiffeomorph_smul",
    "theorem differentialNormalTotalDiffeomorph_localTriv",
    "theorem differentialNormalTotalDiffeomorph_coordChange_eq",
    "theorem differentialNormalTotalDiffeomorph_one_loop_coordChange_eq_neg_id",
)

DIFFERENTIAL_NORMAL_ZERO_NONZERO_STRATIFICATION_DECLARATIONS = (
    "def fixedThroatNormalZeroStratum",
    "def fixedThroatNormalNonzeroStratum",
    "def differentialNormalZeroStratum",
    "def differentialNormalNonzeroStratum",
    "theorem differentialNormalStrata_disjoint",
    "theorem differentialNormalStrata_cover",
    "theorem differentialNormalZeroStratum_eq_range_zeroSection",
    "theorem differentialNormalZeroSection_contMDiff",
    "theorem differentialNormalZeroSection_isEmbedding",
    "theorem differentialNormalNonzeroStratum_isOpen",
    "theorem differentialNormalZeroStratum_isClosed",
    "theorem differentialNormalZeroNonzeroStratification",
)

AMBIENT_TANGENT_ORIENTATION_COCYCLE_DECLARATIONS = (
    "def ambientQuotientLocalChart",
    "def ambientAtlasTransition",
    "theorem ambientAtlasTransition_mem_contDiffGroupoid",
    "def ambientAtlasPartialDiffeomorph",
    "def ambientAtlasTangentTransition",
    "def ambientAtlasDeterminant",
    "theorem ambientAtlasDeterminant_ne_zero",
    "def ambientAtlasOrientationParity",
    "theorem ambientAtlasOrientationParity_eq_zero_iff",
    "theorem ambientAtlasOrientationParity_eq_one_iff",
    "structure AmbientTangentQuadraticAtlasContract",
    "structure AmbientNormalOrientationComparisonAt",
    "theorem normalPinMinus_reduction_eq_ambientParity",
)

AMBIENT_TANGENT_QUADRATIC_REDUCTION_DECLARATIONS = (
    "def ambientCoverEuclideanBilinearForm",
    "def ambientCoverEuclideanQuadraticForm",
    "theorem ambientCoverEuclideanQuadraticForm_posDef",
    "theorem ambientCoverEuclideanQuadraticForm_nondegenerate",
    "def ambientAtlasTransportedQuadraticForm",
    "theorem ambientAtlasTransportedQuadraticForm_posDef",
    "theorem ambientAtlasTransportedQuadraticForm_nondegenerate",
    "def ambientAtlasQuadraticIsometry",
    "structure AmbientOrthonormalAtlasReduction",
    "def AmbientOrthonormalAtlasReduction.toQuadraticAtlasContract",
    "def AmbientOrthonormalAtlasReduction.orthogonalTransition",
    "structure AmbientPinSpinCCechLiftContract",
    "structure AmbientPinSpinCContinuousCechLiftContract",
)

AMBIENT_SPIN_PROJECTION_DECLARATIONS = (
    "theorem ambientCliffordIota_injective",
    "def ambientSpinVectorAction",
    "def ambientSpinVectorLinearMap",
    "def ambientSpinVectorEquiv",
    "theorem ambientSpinVectorAction_preserves_quadraticForm",
    "def ambientSpinQuadraticIsometry",
    "def ambientSpinProjection",
    "theorem ambientSpinProjection_is_orthogonal",
    "def ambientSpinToPin",
    "theorem ambientPinTwistedImage_existsUnique",
    "structure AmbientPinProjectionExtension",
    "structure AmbientSpinCechTransitionLift",
    "def AmbientSpinCechTransitionLift.toPinSpinCCechLiftContract",
)

AMBIENT_SPIN_ORIENTATION_DECLARATIONS = (
    "theorem ambientSpinProjection_det",
)

AMBIENT_SPIN_ATLAS_OBSTRUCTION_DECLARATIONS = (
    "theorem ambientAtlasTransition_cocycle_apply",
    "theorem ambientAtlasTangentTransition_cocycle",
    "theorem ambientOrthogonalTransition_cocycle",
    "structure AmbientSpinOverlapLift",
    "def AmbientSpinOverlapLift.comp",
    "def ambientSpinCechDefect",
    "theorem ambientSpinProjection_cechDefect",
    "def ambientSpinCechKernelDefect",
    "theorem ambientSpinCechDefect_eq_one_iff",
    "def ambientSpinOverlapLiftDifference",
    "theorem ambientSpinOverlapLiftDifference_eq_one_iff",
    "def AmbientSpinOverlapLift.kernelTranslate",
    "theorem AmbientSpinOverlapLift.kernelTranslate_one",
    "theorem AmbientSpinOverlapLift.kernelTranslate_mul",
    "theorem ambientSpinOverlapLiftDifference_kernelTranslate",
    "theorem AmbientSpinOverlapLift.kernelTranslate_injective",
    "def ambientSpinKernelConjugate",
    "def ambientSpinKernelConjugationEquiv",
    "theorem ambientSpinKernelConjugationEquiv_apply",
    "def ambientSpinKernelConjugationRepresentation",
    "theorem ambientSpinKernelConjugationRepresentation_apply",
    "theorem ambientSpinKernelConjugate_eq_iff_commute",
    "theorem ambientSpinKernelConjugationEquiv_eq_one_iff",
    "theorem ambientSpinKernelConjugationRepresentation_eq_one_iff",
    "theorem ambientSpinOverlapLiftDifference_common_kernelTranslate",
    "theorem ambientSpinOverlapLiftDifference_transitive",
    "theorem ambientSpinCechDefect_comp_eq_one",
    "theorem ambientSpinCechDefect_third_kernelTranslate",
    "theorem ambientSpinCechDefect_canonicalThirdCorrection_eq_one",
    "theorem ambientSpinCechDefect_third_kernelTranslate_eq_one_iff",
    "theorem ambientSpinCechCanonicalThirdCorrection_eq_comp",
    "theorem ambientSpinCechDefect_secondThird_kernelTranslate",
    "theorem ambientSpinCechDefect_firstSecond_kernelTranslate",
)

SMOOTH_NORMAL_Z4_ROOT_DECLARATIONS = (
    "def quarterRootRepresentation",
    "theorem quarterRootRepresentation_add",
    "theorem quarterRootRepresentation_square",
    "def fixedThroatNormalZ4RootBundleCore",
    "theorem fixedThroatNormalZ4RootFiber_isVectorBundle",
    "def fixedThroatNormalZ4RootRealBundleCore",
    "theorem fixedThroatNormalZ4RootRealFiber_isContMDiffVectorBundle",
    "theorem complex_and_real_root_coordChange_agree",
    "theorem one_loop_root_transition_square",
    "theorem one_loop_root_transition_fourth",
)

NORMAL_ROOT_PT_CONJUGATION_DECLARATIONS = (
    "theorem conj_normalRootMultiplier",
    "theorem conj_quarterRootRepresentation",
    "def rootPTConjugation",
    "theorem rootPTConjugation_involutive",
    "theorem rootPTConjugation_intertwines",
    "theorem rootPTConjugation_coordChange",
    "theorem rootPTConjugation_double",
)

NORMAL_PIN_MINUS_PRINCIPAL_DECLARATIONS = (
    "def normalPinMinusCoordChange",
    "def fixedThroatNormalPinMinusBundleCore",
    "def fixedThroatNormalPinMinusFiber_isFiberBundle",
    "theorem coordChange_right_equivariant",
    "theorem normalPinMinusRightAction_free",
    "theorem normalPinMinusRightAction_transitive",
    "structure NormalPinMinusPrincipalBundle",
    "def fixedThroatNormalPinMinusPrincipalBundle",
    "theorem one_loop_pinMinus_coordChange",
    "theorem pinMinus_generator_square",
    "theorem pinMinus_generator_fourth",
    "theorem reduce_coordChange_to_orientation",
)

NORMAL_PIN_MINUS_ASSOCIATED_ROOTS_DECLARATIONS = (
    "def pinMinusRootCharacter",
    "theorem pinMinusRootCharacter_square",
    "theorem pinMinusRootCharacter_opposite",
    "def associatedRootPhaseAction",
    "theorem associatedRootPhaseAction_free",
    "theorem associatedRootPhaseAction_transitive",
    "def fixedThroatAssociatedRootPhaseBundleCore",
    "def fixedThroatAssociatedRootPhaseFiber_isFiberBundle",
    "theorem associated_coordChange_from_principal",
    "theorem one_loop_associatedRootPhase_coordChange",
    "theorem associatedRootPhase_generator_square",
    "theorem associatedRootPhase_generator_fourth",
)

GLOBAL_NORMAL_AND_Z4_STATUSES = (
    "fixedThroatNormalGlobalAlgebraicEquivProved",
    "fixedThroatDifferentialNormalTopologicalBundleConstructed",
    "fixedThroatDifferentialNormalContMDiffVectorBundleProved",
    "fixedThroatDifferentialNormalSmoothBundleEquivalenceProved",
    "fixedThroatDifferentialNormalZeroNonzeroStratificationProved",
    "ambientTangentOrientationCocycleProved",
    "ambientTangentQuadraticReductionFrontierProved",
    "ambientSpinProjectionConstructed",
    "ambientSpinProjectionOrientationProved",
    "ambientSpinAtlasCechObstructionProved",
    "fixedThroatNormalZ4RootComplexLineConstructed",
    "fixedThroatNormalZ4RootSmoothRealUnderlierProved",
    "fixedThroatNormalZ4RootSquaresToNormalSignProved",
    "fixedThroatNormalZ4RootPTConjugationProved",
    "fixedThroatNormalPinMinusPrincipalBundleConstructed",
    "fixedThroatNormalPinMinusAssociatedRootsProved",
)

COMPACT_QUOTIENT_DECLARATIONS = (
    "def fundamentalStripProjection",
    "theorem fundamentalStripProjection_continuous",
    "theorem fundamentalStripProjection_surjective",
    "def mappingTorusCompactSpace",
    "def reflectedSphereQuotientCompactSpace",
    "def fixedThroatQuotientCompactSpace",
)

COMPACT_QUOTIENT_STATUSES = (
    "effectiveMappingTorusCompactProved",
    "effectiveThroatCompactProved",
)

THROAT_COMPLEMENT_CONNECTED_STATUSES = (
    "positiveAndNegativeSphereSidesPathConnectedProved",
    "positiveCoverSidePathConnectedProved",
    "effectiveThroatComplementPathConnectedProved",
    "effectiveThroatComplementConnectedProved",
)


def assert_d8_topology_integrity(repo_root: Path = REPO_ROOT) -> None:
    gate = (repo_root / GATE).read_text(encoding="utf-8")
    normal_line_gate = (repo_root / NORMAL_LINE_GATE).read_text(encoding="utf-8")
    pt_gate = (repo_root / PT_GATE).read_text(encoding="utf-8")
    orientation_double_gate = (repo_root / ORIENTATION_DOUBLE_GATE).read_text(
        encoding="utf-8"
    )
    throat_complement_gate = (repo_root / THROAT_COMPLEMENT_GATE).read_text(
        encoding="utf-8"
    )
    throat_complement_connected_gate = (
        repo_root / THROAT_COMPLEMENT_CONNECTED_GATE
    ).read_text(encoding="utf-8")
    smooth_atlas_frontier_gate = (
        repo_root / SMOOTH_ATLAS_FRONTIER_GATE
    ).read_text(encoding="utf-8")
    smooth_deck_descent_gate = (
        repo_root / SMOOTH_DECK_DESCENT_GATE
    ).read_text(encoding="utf-8")
    smooth_quotient_manifold_gate = (
        repo_root / SMOOTH_QUOTIENT_MANIFOLD_GATE
    ).read_text(encoding="utf-8")
    smooth_pt_gate = (repo_root / SMOOTH_PT_GATE).read_text(encoding="utf-8")
    smooth_throat_embedding_gate = (
        repo_root / SMOOTH_THROAT_EMBEDDING_GATE
    ).read_text(encoding="utf-8")
    is_smooth_embedding_gate = (
        repo_root / IS_SMOOTH_EMBEDDING_GATE
    ).read_text(encoding="utf-8")
    smooth_normal_vector_bundle_gate = (
        repo_root / SMOOTH_NORMAL_VECTOR_BUNDLE_GATE
    ).read_text(encoding="utf-8")
    global_normal_equivalence_gate = (
        repo_root / GLOBAL_NORMAL_EQUIVALENCE_GATE
    ).read_text(encoding="utf-8")
    differential_normal_topological_bundle_gate = (
        repo_root / DIFFERENTIAL_NORMAL_TOPOLOGICAL_BUNDLE_GATE
    ).read_text(encoding="utf-8")
    differential_normal_smooth_bundle_equivalence_gate = (
        repo_root / DIFFERENTIAL_NORMAL_SMOOTH_BUNDLE_EQUIVALENCE_GATE
    ).read_text(encoding="utf-8")
    differential_normal_zero_nonzero_stratification_gate = (
        repo_root / DIFFERENTIAL_NORMAL_ZERO_NONZERO_STRATIFICATION_GATE
    ).read_text(encoding="utf-8")
    ambient_tangent_orientation_cocycle_gate = (
        repo_root / AMBIENT_TANGENT_ORIENTATION_COCYCLE_GATE
    ).read_text(encoding="utf-8")
    ambient_tangent_quadratic_reduction_gate = (
        repo_root / AMBIENT_TANGENT_QUADRATIC_REDUCTION_GATE
    ).read_text(encoding="utf-8")
    ambient_spin_projection_gate = (
        repo_root / AMBIENT_SPIN_PROJECTION_GATE
    ).read_text(encoding="utf-8")
    ambient_spin_orientation_gate = (
        repo_root / AMBIENT_SPIN_ORIENTATION_GATE
    ).read_text(encoding="utf-8")
    ambient_spin_atlas_obstruction_gate = (
        repo_root / AMBIENT_SPIN_ATLAS_OBSTRUCTION_GATE
    ).read_text(encoding="utf-8")
    smooth_normal_z4_root_gate = (
        repo_root / SMOOTH_NORMAL_Z4_ROOT_GATE
    ).read_text(encoding="utf-8")
    normal_root_pt_conjugation_gate = (
        repo_root / NORMAL_ROOT_PT_CONJUGATION_GATE
    ).read_text(encoding="utf-8")
    normal_pin_minus_principal_gate = (
        repo_root / NORMAL_PIN_MINUS_PRINCIPAL_GATE
    ).read_text(encoding="utf-8")
    normal_pin_minus_associated_roots_gate = (
        repo_root / NORMAL_PIN_MINUS_ASSOCIATED_ROOTS_GATE
    ).read_text(encoding="utf-8")
    facade = (repo_root / FACADE).read_text(encoding="utf-8")
    compact_quotient_gate = (repo_root / COMPACT_QUOTIENT_GATE).read_text(
        encoding="utf-8"
    )

    for declaration in DECLARATIONS:
        if declaration not in gate:
            raise AssertionError(f"missing D8 declaration: {declaration}")
    if re.search(r"\b(?:sorry|admit|axiom)\b", gate):
        raise AssertionError("proof placeholder found in D8 quotient gate")
    if "IsManifold" in gate:
        raise AssertionError("D8 quotient gate overclaims a manifold theorem")

    gate_import = "Gates.P0EFTJanusMappingTorusQuotient"
    if facade.count(gate_import) != 1:
        raise AssertionError("D8 facade omits the quotient gate")
    for status in STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits status: {status}")

    for declaration in NORMAL_LINE_DECLARATIONS:
        if declaration not in normal_line_gate:
            raise AssertionError(f"missing D8 associated-line declaration: {declaration}")
    if re.search(r"\b(?:sorry|admit|axiom)\b", normal_line_gate):
        raise AssertionError("proof placeholder found in D8 associated-line gate")
    for overclaim in ("IsManifold", "VectorBundle"):
        if overclaim in normal_line_gate:
            raise AssertionError(f"D8 associated-line gate overclaims {overclaim}")

    normal_line_import = "Gates.P0EFTJanusMappingTorusNormalLine"
    if facade.count(normal_line_import) != 1:
        raise AssertionError("D8 facade omits the associated-line gate")
    if facade.count("associatedNormalLineQuotientCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits the associated-line milestone")
    for status in NORMAL_LINE_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits associated-line status: {status}")

    for declaration in PT_DECLARATIONS:
        if declaration not in pt_gate:
            raise AssertionError(f"missing D8 PT declaration: {declaration}")
    if re.search(r"\b(?:sorry|admit|axiom)\b", pt_gate):
        raise AssertionError("proof placeholder found in D8 PT gate")
    pt_import = "Gates.P0EFTJanusMappingTorusPTInvolution"
    if facade.count(pt_import) != 1:
        raise AssertionError("D8 facade omits the mapping-torus PT gate")
    if facade.count("effectiveMappingTorusPTCoreClosed s") != 1:
        raise AssertionError("D8 core omits the mapping-torus PT milestone")
    for status in PT_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits PT status: {status}")

    for declaration in ORIENTATION_DOUBLE_DECLARATIONS:
        if declaration not in orientation_double_gate:
            raise AssertionError(
                f"missing D8 orientation-double-cover declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", orientation_double_gate):
        raise AssertionError("proof placeholder found in D8 orientation-double-cover gate")
    for overclaim in ("IsManifold", "VectorBundle"):
        if overclaim in orientation_double_gate:
            raise AssertionError(
                f"D8 orientation-double-cover gate overclaims {overclaim}"
            )
    orientation_double_import = "Gates.P0EFTJanusMappingTorusOrientationDoubleCover"
    if facade.count(orientation_double_import) != 1:
        raise AssertionError("D8 facade omits the orientation-double-cover gate")
    if facade.count("effectiveThroatOrientationDoubleCoverCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits the orientation-double-cover milestone")
    for status in ORIENTATION_DOUBLE_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits orientation-double-cover status: {status}"
            )

    for declaration in THROAT_COMPLEMENT_DECLARATIONS:
        if declaration not in throat_complement_gate:
            raise AssertionError(
                f"missing D8 throat-complement declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", throat_complement_gate):
        raise AssertionError("proof placeholder found in D8 throat-complement gate")
    for overclaim in ("IsManifold", "VectorBundle", "IsConnected", "IsPreconnected"):
        if overclaim in throat_complement_gate:
            raise AssertionError(f"D8 throat-complement gate overclaims {overclaim}")
    complement_import = "Gates.P0EFTJanusMappingTorusThroatComplementSides"
    if facade.count(complement_import) != 1:
        raise AssertionError("D8 facade omits the throat-complement gate")
    if facade.count("effectiveThroatComplementSidesCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits the throat-complement milestone")
    for status in THROAT_COMPLEMENT_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits throat-complement status: {status}"
            )

    for declaration in THROAT_COMPLEMENT_CONNECTED_DECLARATIONS:
        if declaration not in throat_complement_connected_gate:
            raise AssertionError(
                f"missing D8 connected-complement declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", throat_complement_connected_gate):
        raise AssertionError("proof placeholder found in D8 connected-complement gate")
    connected_import = "Gates.P0EFTJanusMappingTorusThroatComplementConnected"
    if facade.count(connected_import) != 1:
        raise AssertionError("D8 facade omits the connected-complement gate")
    if facade.count("effectiveThroatComplementConnectedCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits connected-complement milestone")
    for status in THROAT_COMPLEMENT_CONNECTED_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits connected-complement status: {status}"
            )

    for declaration in SMOOTH_ATLAS_FRONTIER_DECLARATIONS:
        if declaration not in smooth_atlas_frontier_gate:
            raise AssertionError(
                f"missing D8 smooth-atlas-frontier declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_atlas_frontier_gate):
        raise AssertionError("proof placeholder found in D8 smooth-atlas frontier")
    smooth_frontier_import = "Gates.P0EFTJanusMappingTorusSmoothAtlasFrontier"
    if facade.count(smooth_frontier_import) != 1:
        raise AssertionError("D8 facade omits the smooth-atlas frontier gate")
    if facade.count("mappingTorusSmoothAtlasFrontierCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth-atlas frontier milestone")
    for status in SMOOTH_ATLAS_FRONTIER_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits smooth-atlas status: {status}")

    for declaration in SMOOTH_DECK_DESCENT_DECLARATIONS:
        if declaration not in smooth_deck_descent_gate:
            raise AssertionError(
                f"missing D8 smooth-deck descent declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_deck_descent_gate):
        raise AssertionError("proof placeholder found in D8 smooth-deck descent gate")
    smooth_descent_import = (
        "import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation."
        "Gates.P0EFTJanusMappingTorusSmoothQuotient\n"
    )
    if facade.count(smooth_descent_import) != 1:
        raise AssertionError("D8 facade omits the smooth-deck descent gate")
    if facade.count("mappingTorusSmoothDeckDescentFrontierClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth-deck descent milestone")
    status = "smoothDeckActionsAndAtlasTransitionsProved"
    if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
        raise AssertionError(f"D8 facade omits smooth-deck status: {status}")

    for declaration in SMOOTH_QUOTIENT_MANIFOLD_DECLARATIONS:
        if declaration not in smooth_quotient_manifold_gate:
            raise AssertionError(
                f"missing D8 smooth-quotient-manifold declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_quotient_manifold_gate):
        raise AssertionError("proof placeholder found in D8 smooth quotient manifold")
    smooth_quotient_import = (
        "import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation."
        "Gates.P0EFTJanusMappingTorusSmoothQuotientManifold\n"
    )
    if facade.count(smooth_quotient_import) != 1:
        raise AssertionError("D8 facade omits the smooth quotient manifold gate")
    if facade.count("mappingTorusSmoothQuotientManifoldCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth quotient manifold milestone")
    for status in SMOOTH_QUOTIENT_MANIFOLD_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits smooth quotient manifold status: {status}"
            )

    for declaration in SMOOTH_PT_DECLARATIONS:
        if declaration not in smooth_pt_gate:
            raise AssertionError(f"missing D8 smooth-PT declaration: {declaration}")
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_pt_gate):
        raise AssertionError("proof placeholder found in D8 smooth-PT gate")
    smooth_pt_import = "Gates.P0EFTJanusMappingTorusSmoothPTInvolution"
    if facade.count(smooth_pt_import) != 1:
        raise AssertionError("D8 facade omits the smooth-PT gate")
    if facade.count("mappingTorusSmoothPTCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth-PT milestone")
    for status in SMOOTH_PT_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits smooth-PT status: {status}")

    for declaration in SMOOTH_THROAT_EMBEDDING_DECLARATIONS:
        if declaration not in smooth_throat_embedding_gate:
            raise AssertionError(
                f"missing D8 smooth-throat declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_throat_embedding_gate):
        raise AssertionError("proof placeholder found in D8 smooth-throat gate")
    smooth_throat_import = "Gates.P0EFTJanusMappingTorusSmoothThroatEmbedding"
    if facade.count(smooth_throat_import) != 1:
        raise AssertionError("D8 facade omits the smooth-throat gate")
    if facade.count("fixedThroatSmoothEmbeddingFrontierClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth-throat milestone")
    for status in SMOOTH_THROAT_EMBEDDING_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits smooth-throat status: {status}")

    for declaration in IS_SMOOTH_EMBEDDING_DECLARATIONS:
        if declaration not in is_smooth_embedding_gate:
            raise AssertionError(
                f"missing D8 IsSmoothEmbedding declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", is_smooth_embedding_gate):
        raise AssertionError("proof placeholder found in D8 IsSmoothEmbedding gate")
    is_smooth_embedding_import = "Gates.P0EFTJanusMappingTorusIsSmoothEmbedding"
    if facade.count(is_smooth_embedding_import) != 1:
        raise AssertionError("D8 facade omits the IsSmoothEmbedding gate")
    for status in IS_SMOOTH_EMBEDDING_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits IsSmoothEmbedding status: {status}")

    for declaration in SMOOTH_NORMAL_VECTOR_BUNDLE_DECLARATIONS:
        if declaration not in smooth_normal_vector_bundle_gate:
            raise AssertionError(
                f"missing D8 smooth-normal-bundle declaration: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b", smooth_normal_vector_bundle_gate
    ):
        raise AssertionError("proof placeholder found in D8 smooth normal bundle")
    smooth_normal_import = "Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle"
    if facade.count(smooth_normal_import) != 1:
        raise AssertionError("D8 facade omits the smooth normal vector-bundle gate")
    if facade.count("fixedThroatSmoothNormalBundleClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth normal bundle milestone")
    for status in SMOOTH_NORMAL_VECTOR_BUNDLE_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits smooth-normal-bundle status: {status}"
            )

    for declaration in GLOBAL_NORMAL_EQUIVALENCE_DECLARATIONS:
        if declaration not in global_normal_equivalence_gate:
            raise AssertionError(
                f"missing D8 global-normal declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", global_normal_equivalence_gate):
        raise AssertionError("proof placeholder found in D8 global normal comparison")
    global_normal_import = "Gates.P0EFTJanusMappingTorusGlobalNormalEquivalence"
    if facade.count(global_normal_import) != 1:
        raise AssertionError("D8 facade omits the global normal comparison gate")
    for declaration in DIFFERENTIAL_NORMAL_TOPOLOGICAL_BUNDLE_DECLARATIONS:
        if declaration not in differential_normal_topological_bundle_gate:
            raise AssertionError(
                f"missing D8 differential-normal bundle declaration: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b", differential_normal_topological_bundle_gate
    ):
        raise AssertionError("proof placeholder found in D8 differential-normal bundle")
    differential_normal_bundle_import = (
        "Gates.P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle"
    )
    if facade.count(differential_normal_bundle_import) != 1:
        raise AssertionError("D8 facade omits the differential-normal bundle gate")
    for declaration in DIFFERENTIAL_NORMAL_SMOOTH_BUNDLE_EQUIVALENCE_DECLARATIONS:
        if declaration not in differential_normal_smooth_bundle_equivalence_gate:
            raise AssertionError(
                f"missing D8 differential-normal smooth equivalence: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b",
        differential_normal_smooth_bundle_equivalence_gate,
    ):
        raise AssertionError(
            "proof placeholder found in D8 differential-normal smooth equivalence"
        )
    differential_normal_smooth_import = (
        "Gates.P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence"
    )
    if facade.count(differential_normal_smooth_import) != 1:
        raise AssertionError(
            "D8 facade omits the differential-normal smooth equivalence gate"
        )
    for declaration in DIFFERENTIAL_NORMAL_ZERO_NONZERO_STRATIFICATION_DECLARATIONS:
        if declaration not in differential_normal_zero_nonzero_stratification_gate:
            raise AssertionError(
                f"missing D8 differential-normal stratum declaration: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b",
        differential_normal_zero_nonzero_stratification_gate,
    ):
        raise AssertionError(
            "proof placeholder found in D8 differential-normal stratification"
        )
    differential_normal_strata_import = (
        "Gates.P0EFTJanusMappingTorusDifferentialNormalZeroNonzeroStratification"
    )
    if facade.count(differential_normal_strata_import) != 1:
        raise AssertionError(
            "D8 facade omits the differential-normal stratification gate"
        )

    for declaration in AMBIENT_TANGENT_ORIENTATION_COCYCLE_DECLARATIONS:
        if declaration not in ambient_tangent_orientation_cocycle_gate:
            raise AssertionError(
                f"missing D8 ambient-tangent orientation declaration: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b", ambient_tangent_orientation_cocycle_gate
    ):
        raise AssertionError(
            "proof placeholder found in D8 ambient-tangent orientation gate"
        )
    ambient_tangent_orientation_import = (
        "Gates.P0EFTJanusMappingTorusAmbientTangentOrientationCocycle"
    )
    if facade.count(ambient_tangent_orientation_import) != 1:
        raise AssertionError(
            "D8 facade omits the ambient-tangent orientation gate"
        )

    for declaration in AMBIENT_TANGENT_QUADRATIC_REDUCTION_DECLARATIONS:
        if declaration not in ambient_tangent_quadratic_reduction_gate:
            raise AssertionError(
                f"missing D8 ambient quadratic-reduction declaration: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b", ambient_tangent_quadratic_reduction_gate
    ):
        raise AssertionError(
            "proof placeholder found in D8 ambient quadratic-reduction gate"
        )
    ambient_quadratic_reduction_import = (
        "Gates.P0EFTJanusMappingTorusAmbientTangentQuadraticReduction"
    )
    if facade.count(ambient_quadratic_reduction_import) != 1:
        raise AssertionError(
            "D8 facade omits the ambient quadratic-reduction gate"
        )

    for declaration in AMBIENT_SPIN_PROJECTION_DECLARATIONS:
        if declaration not in ambient_spin_projection_gate:
            raise AssertionError(
                f"missing D8 ambient Spin-projection declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", ambient_spin_projection_gate):
        raise AssertionError(
            "proof placeholder found in D8 ambient Spin-projection gate"
        )
    ambient_spin_projection_import = (
        "Gates.P0EFTJanusMappingTorusAmbientSpinProjection"
    )
    if facade.count(ambient_spin_projection_import) != 1:
        raise AssertionError("D8 facade omits the ambient Spin-projection gate")

    for declaration in AMBIENT_SPIN_ORIENTATION_DECLARATIONS:
        if declaration not in ambient_spin_orientation_gate:
            raise AssertionError(
                f"missing D8 ambient Spin-orientation declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", ambient_spin_orientation_gate):
        raise AssertionError(
            "proof placeholder found in D8 ambient Spin-orientation gate"
        )
    ambient_spin_orientation_import = (
        "Gates.P0EFTJanusMappingTorusAmbientSpinOrientation"
    )
    if facade.count(ambient_spin_orientation_import) != 1:
        raise AssertionError("D8 facade omits the ambient Spin-orientation gate")

    for declaration in AMBIENT_SPIN_ATLAS_OBSTRUCTION_DECLARATIONS:
        if declaration not in ambient_spin_atlas_obstruction_gate:
            raise AssertionError(
                f"missing D8 ambient Spin-atlas declaration: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b", ambient_spin_atlas_obstruction_gate
    ):
        raise AssertionError(
            "proof placeholder found in D8 ambient Spin-atlas gate"
        )
    ambient_spin_atlas_obstruction_import = (
        "Gates.P0EFTJanusMappingTorusAmbientSpinAtlasObstruction"
    )
    if facade.count(ambient_spin_atlas_obstruction_import) != 1:
        raise AssertionError("D8 facade omits the ambient Spin-atlas gate")

    for declaration in SMOOTH_NORMAL_Z4_ROOT_DECLARATIONS:
        if declaration not in smooth_normal_z4_root_gate:
            raise AssertionError(
                f"missing D8 smooth normal-Z4 declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_normal_z4_root_gate):
        raise AssertionError("proof placeholder found in D8 smooth normal-Z4 gate")
    smooth_normal_z4_import = (
        "Gates.P0EFTJanusMappingTorusSmoothNormalZ4RootBundle"
    )
    if facade.count(smooth_normal_z4_import) != 1:
        raise AssertionError("D8 facade omits the smooth normal-Z4 root gate")
    for declaration in NORMAL_ROOT_PT_CONJUGATION_DECLARATIONS:
        if declaration not in normal_root_pt_conjugation_gate:
            raise AssertionError(
                f"missing D8 normal-root PT declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", normal_root_pt_conjugation_gate):
        raise AssertionError("proof placeholder found in D8 normal-root PT gate")
    normal_root_pt_import = (
        "Gates.P0EFTJanusMappingTorusNormalRootPTConjugation"
    )
    if facade.count(normal_root_pt_import) != 1:
        raise AssertionError("D8 facade omits the normal-root PT gate")
    for declaration in NORMAL_PIN_MINUS_PRINCIPAL_DECLARATIONS:
        if declaration not in normal_pin_minus_principal_gate:
            raise AssertionError(
                f"missing D8 normal Pin-minus declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", normal_pin_minus_principal_gate):
        raise AssertionError("proof placeholder found in D8 normal Pin-minus gate")
    normal_pin_minus_import = (
        "Gates.P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle"
    )
    if facade.count(normal_pin_minus_import) != 1:
        raise AssertionError("D8 facade omits the normal Pin-minus principal gate")
    for declaration in NORMAL_PIN_MINUS_ASSOCIATED_ROOTS_DECLARATIONS:
        if declaration not in normal_pin_minus_associated_roots_gate:
            raise AssertionError(
                f"missing D8 associated normal-root declaration: {declaration}"
            )
    if re.search(
        r"\b(?:sorry|admit|axiom)\b", normal_pin_minus_associated_roots_gate
    ):
        raise AssertionError("proof placeholder found in D8 associated roots gate")
    associated_roots_import = (
        "Gates.P0EFTJanusMappingTorusNormalPinMinusAssociatedRoots"
    )
    if facade.count(associated_roots_import) != 1:
        raise AssertionError("D8 facade omits the associated normal-root gate")
    for status in GLOBAL_NORMAL_AND_Z4_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits global-normal/Z4 status: {status}"
            )


    for declaration in COMPACT_QUOTIENT_DECLARATIONS:
        if declaration not in compact_quotient_gate:
            raise AssertionError(
                f"missing D8 compact-quotient declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", compact_quotient_gate):
        raise AssertionError("proof placeholder found in D8 compact quotient gate")
    compact_import = "Gates.P0EFTJanusMappingTorusCompactQuotient"
    if facade.count(compact_import) != 1:
        raise AssertionError("D8 facade omits the compact quotient gate")
    if facade.count("effectiveQuotientCompactnessClosed s") != 1:
        raise AssertionError("D8 smooth core omits compactness milestone")
    for status in COMPACT_QUOTIENT_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits compact-quotient status: {status}"
            )

def run_audit() -> None:
    assert_d8_topology_integrity()
    print("D8 topology integrity audit: all checks passed")


if __name__ == "__main__":
    run_audit()

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D

/-!
# Algebraic compatibility of the minimal physical graph projections

The diagonal smooth core was assembled by inserting metric, Abelian,
primitive-matter and full-LL directions in disjoint typed slots.  Consequently
extracting the matter and LL slots from the resulting minimal physical tangent
must recover the original finite matter packet and full LL smooth direction.

This file records that compatibility directly from the existing insertion
maps.  It removes the corresponding fields from the analytic frontier: only
the smooth SpinC graph realization and the two graph-norm bounds remain to be
proved.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The matter component of the corrected diagonal tangent is exactly the
finite primitive SpinC synthesis used to build that core. -/
theorem diagonalExtendedBulkMinimalPhysicalTangent_matter
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis core).1.2 =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        core.2.2.1 := by
  unfold diagonalExtendedBulkMinimalPhysicalTangentLinearMap
    diagonalExtendedBulkGaugeFixedTangentLinearMap
    diagonalDiffeomorphismGaugeFixedTangentLinearMap
    globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
    extendedMatterGaugeFixedTangentLinearMap
    extendedLLGaugeFixedTangentLinearMap
    extendedMatterMinimalTangentLinearMap
    extendedLLMinimalTangentLinearMap
    globalCandidateABulkMatterPhysicalTangentLinearMap
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
    globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
    globalMetricPerturbationMinimalPhysicalTangentLinearMap
    globalMetricPerturbationPhysicalTangentLinearMap
    globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
    gaugeVariationPairMinimalPhysicalTangentLinearMap
    gaugeVariationPairPhysicalTangentLinearMap
    fullLLSmoothPhysicalTangentLinearMap
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.coe_add,
    LinearMap.fst_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    Prod.fst_add, Prod.snd_add, zero_add, add_zero]

/-- The three LL slots of the corrected diagonal tangent are exactly the full
LL smooth direction used in the diagonal core. -/
theorem diagonalExtendedBulkMinimalPhysicalTangent_fullLL
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod configuration
        analysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      core.2.2.2 := by
  apply Prod.ext
  · apply Prod.ext
    · unfold globalMinimalPhysicalFullLLSmoothLinearMap
        diagonalExtendedBulkMinimalPhysicalTangentLinearMap
        diagonalExtendedBulkGaugeFixedTangentLinearMap
        diagonalDiffeomorphismGaugeFixedTangentLinearMap
        globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
        extendedMatterGaugeFixedTangentLinearMap
        extendedLLGaugeFixedTangentLinearMap
        extendedMatterMinimalTangentLinearMap
        extendedLLMinimalTangentLinearMap
        globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
        globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
        globalMetricPerturbationMinimalPhysicalTangentLinearMap
        globalMetricPerturbationPhysicalTangentLinearMap
        globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
        globalCandidateABulkMatterPhysicalTangentLinearMap
        gaugeVariationPairMinimalPhysicalTangentLinearMap
        gaugeVariationPairPhysicalTangentLinearMap
        gaugeVariationPairGeneralMetricLinearMap
        gaugeVariationPairMatterFreeLinearMap
        gaugeVariationPairCompleteLinearMap
        gaugeVariationPairIndependentLinearMap gaugeOnlyIndependentVariation
        globalMetricPerturbationGeneralMetricLinearMap
        globalMetricPerturbationMatterFreeLinearMap
        globalMetricPerturbationCompleteLinearMap
        fullLLSmoothPhysicalTangentLinearMap
        fullLLSmoothGeneralMetricLinearMap fullLLSmoothMatterFreeLinearMap
        fullLLSmoothCompleteLinearMap fullLLSmoothIndependentLinearMap
        independentCompleteVariationLinearMap independentCompleteVariation
        GlobalPhysicalFieldTangent.completeVariation LLH1Smooth.ofTest
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Submodule.coe_add,
        LinearMap.fst_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        Prod.fst_add, Prod.snd_add, zero_add, add_zero]
      change (0 : _) + 0 + core.2.2.2.1.1 = core.2.2.2.1.1
      simp
    · unfold globalMinimalPhysicalFullLLSmoothLinearMap
        diagonalExtendedBulkMinimalPhysicalTangentLinearMap
        diagonalExtendedBulkGaugeFixedTangentLinearMap
        diagonalDiffeomorphismGaugeFixedTangentLinearMap
        globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
        extendedMatterGaugeFixedTangentLinearMap
        extendedLLGaugeFixedTangentLinearMap
        extendedMatterMinimalTangentLinearMap
        extendedLLMinimalTangentLinearMap
        globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
        globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
        globalMetricPerturbationMinimalPhysicalTangentLinearMap
        globalMetricPerturbationPhysicalTangentLinearMap
        globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
        globalCandidateABulkMatterPhysicalTangentLinearMap
        gaugeVariationPairMinimalPhysicalTangentLinearMap
        gaugeVariationPairPhysicalTangentLinearMap
        gaugeVariationPairGeneralMetricLinearMap
        gaugeVariationPairMatterFreeLinearMap
        gaugeVariationPairCompleteLinearMap
        gaugeVariationPairIndependentLinearMap gaugeOnlyIndependentVariation
        globalMetricPerturbationGeneralMetricLinearMap
        globalMetricPerturbationMatterFreeLinearMap
        globalMetricPerturbationCompleteLinearMap
        fullLLSmoothPhysicalTangentLinearMap
        fullLLSmoothGeneralMetricLinearMap fullLLSmoothMatterFreeLinearMap
        fullLLSmoothCompleteLinearMap fullLLSmoothIndependentLinearMap
        independentCompleteVariationLinearMap independentCompleteVariation
        GlobalPhysicalFieldTangent.completeVariation LLH1Smooth.ofTest
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Submodule.coe_add,
        LinearMap.fst_apply, LinearMap.inl_apply, LinearMap.inr_apply,
        Prod.fst_add, Prod.snd_add, zero_add, add_zero]
      change (0 : _) + 0 + core.2.2.2.1.2 = core.2.2.2.1.2
      simp
  · apply LLH1Smooth.ext
    unfold globalMinimalPhysicalFullLLSmoothLinearMap
      diagonalExtendedBulkMinimalPhysicalTangentLinearMap
      diagonalExtendedBulkGaugeFixedTangentLinearMap
      diagonalDiffeomorphismGaugeFixedTangentLinearMap
      globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
      extendedMatterGaugeFixedTangentLinearMap
      extendedLLGaugeFixedTangentLinearMap
      extendedMatterMinimalTangentLinearMap
      extendedLLMinimalTangentLinearMap
      globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
      globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
      globalMetricPerturbationMinimalPhysicalTangentLinearMap
      globalMetricPerturbationPhysicalTangentLinearMap
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
      globalCandidateABulkMatterPhysicalTangentLinearMap
      gaugeVariationPairMinimalPhysicalTangentLinearMap
      gaugeVariationPairPhysicalTangentLinearMap
      gaugeVariationPairGeneralMetricLinearMap
      gaugeVariationPairMatterFreeLinearMap
      gaugeVariationPairCompleteLinearMap
      gaugeVariationPairIndependentLinearMap gaugeOnlyIndependentVariation
      globalMetricPerturbationGeneralMetricLinearMap
      globalMetricPerturbationMatterFreeLinearMap
      globalMetricPerturbationCompleteLinearMap
      fullLLSmoothPhysicalTangentLinearMap
      fullLLSmoothGeneralMetricLinearMap fullLLSmoothMatterFreeLinearMap
      fullLLSmoothCompleteLinearMap fullLLSmoothIndependentLinearMap
      independentCompleteVariationLinearMap independentCompleteVariation
      GlobalPhysicalFieldTangent.completeVariation LLH1Smooth.ofTest
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.coe_add,
      LinearMap.fst_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      Prod.fst_add, Prod.snd_add, LLH1Smooth.toTest_add,
      LLH1Smooth.toTest_zero, zero_add, add_zero]
    change (0 : _) + 0 + core.2.2.2.2.toTest = core.2.2.2.2.toTest
    simp

/-- The canonical smooth matter realization recovers the existing finite graph
point on the diagonal core. -/
theorem globalMinimalPhysicalMatterGraphLinearMap_diagonalCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
        couplings.matterMassSquared realization
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared core.2.2.1 := by
  unfold globalMinimalPhysicalMatterGraphLinearMap
    globalMinimalPhysicalSpinCMatterLinearMap
  simp only [LinearMap.comp_apply]
  change realization.toGraph
      ((diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core).1.2) = _
  rw [diagonalExtendedBulkMinimalPhysicalTangent_matter period hPeriod
    configuration data analysis core]
  exact realization.finite_compatibility core.2.2.1

/-- The canonical full-LL graph projection recovers the existing full LL graph
point on the diagonal core. -/
theorem globalMinimalPhysicalLLGraphLinearMap_diagonalCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
        analysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        core.2.2.2 := by
  unfold globalMinimalPhysicalLLGraphLinearMap
  simp only [LinearMap.comp_apply]
  change globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
      (globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod configuration
        analysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core)) = _
  rw [diagonalExtendedBulkMinimalPhysicalTangent_fullLL period hPeriod
    configuration data analysis core]

/-- The former core-compatibility contract is now constructed without an
additional hypothesis. -/
def globalMinimalPhysicalMatterLLGraphCoreCompatibility
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) :
    GlobalMinimalPhysicalMatterLLGraphCoreCompatibility4D period hPeriod
      configuration data analysis realization where
  matter := globalMinimalPhysicalMatterGraphLinearMap_diagonalCore period hPeriod
    configuration data analysis realization
  ll := globalMinimalPhysicalLLGraphLinearMap_diagonalCore period hPeriod
    configuration data analysis

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D
end JanusFormal

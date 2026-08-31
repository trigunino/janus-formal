import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D

/-!
# Kernel saturation of the minimal physical reduced Hilbert core

The common completion retains the two metric graph coordinates, the Abelian
potential graph coordinate, the matter graph and the full LL graph.  Their
continuous product projection forgets only the typed BRST nonminimal slots.
It therefore separates the canonical minimal physical quotient core and shows
that closing its null space creates no additional smooth null vectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D

variable (period : Real) (hPeriod : period ≠ 0)

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

private abbrev Metric :=
  globalCandidateAMetricBySector period hPeriod data

local instance saturationCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (Metric period hPeriod configuration data) couplings.matterMassSquared data
      analysis

local instance saturationCommonInnerProductSpace : InnerProductSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (Metric period hPeriod configuration data) couplings.matterMassSquared data
      analysis

local instance saturationCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (saturationCommonInnerProductSpace period hPeriod configuration data
    analysis).toNormedSpace

local instance saturationCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (saturationCommonNormedSpace period hPeriod configuration data
    analysis).toModule

/-- Completed coordinates that remain after forgetting only the typed
nonminimal BRST directions. -/
abbrev GlobalCandidateAMinimalPhysicalFeatureHilbert :=
  (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
      (Metric period hPeriod configuration data .plus) ×
    GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
      (Metric period hPeriod configuration data .minus)) ×
  (GlobalPairedAbelianLorenzGraphAmbient period hPeriod ×
    (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared ×
      GlobalFullLLGraphHilbert period hPeriod data analysis))

/-- Continuous projection from the common augmented completion to all genuine
minimal physical graph coordinates. -/
def globalCandidateAMinimalPhysicalFeatureProjection :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      GlobalCandidateAMinimalPhysicalFeatureHilbert period hPeriod
        configuration data analysis := by
  let legacy :=
    (diagonalExtendedBulkL2Equiv period hPeriod
      (Metric period hPeriod configuration data) couplings.matterMassSquared
        data analysis).toContinuousLinearMap
  let diffeomorphism :=
    (ContinuousLinearMap.fst Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
        hPeriod (Metric period hPeriod configuration data))
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
          (Metric period hPeriod configuration data) ×
        (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
            couplings.matterMassSquared ×
          GlobalFullLLGraphHilbert period hPeriod data analysis))).comp legacy
  let tail :=
    (ContinuousLinearMap.snd Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
        hPeriod (Metric period hPeriod configuration data))
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
          (Metric period hPeriod configuration data) ×
        (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
            couplings.matterMassSquared ×
          GlobalFullLLGraphHilbert period hPeriod data analysis))).comp legacy
  let abelian :=
    (ContinuousLinearMap.fst Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (Metric period hPeriod configuration data))
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
          couplings.matterMassSquared ×
        GlobalFullLLGraphHilbert period hPeriod data analysis)).comp tail
  let matterLL :=
    (ContinuousLinearMap.snd Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (Metric period hPeriod configuration data))
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
          couplings.matterMassSquared ×
        GlobalFullLLGraphHilbert period hPeriod data analysis)).comp tail
  let plusMetric :=
    (globalDiffeomorphismOffShellMetricProjection period hPeriod
      (Metric period hPeriod configuration data .plus)).comp
        ((globalCandidateADiagonalDiffeomorphismOffShellPlusProjection period
          hPeriod (Metric period hPeriod configuration data)).comp
            diffeomorphism)
  let minusMetric :=
    (globalDiffeomorphismOffShellMetricProjection period hPeriod
      (Metric period hPeriod configuration data .minus)).comp
        ((globalCandidateADiagonalDiffeomorphismOffShellMinusProjection period
          hPeriod (Metric period hPeriod configuration data)).comp
            diffeomorphism)
  let potential :=
    (globalPairedAbelianOffShellPotentialAmbientProjection period hPeriod
      (Metric period hPeriod configuration data)).comp abelian
  let matter :=
    (ContinuousLinearMap.fst Real
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared)
      (GlobalFullLLGraphHilbert period hPeriod data analysis)).comp matterLL
  let ll :=
    (ContinuousLinearMap.snd Real
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared)
      (GlobalFullLLGraphHilbert period hPeriod data analysis)).comp matterLL
  exact (plusMetric.prod minusMetric).prod (potential.prod (matter.prod ll))

@[simp]
theorem globalCandidateAMinimalPhysicalFeatureProjection_smooth
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis core) =
      ((globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
          (Metric period hPeriod configuration data .plus)
          (core.1.metricPerturbation .plus),
        globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
          (Metric period hPeriod configuration data .minus)
          (core.1.metricPerturbation .minus)),
        (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod
          (Metric period hPeriod configuration data) core.2.1.potential,
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared core.2.2.1,
            globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
              core.2.2.2))) := by
  rfl

@[simp]
theorem diagonalExtendedBulkMinimalPhysicalTangent_metric
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core).1).fullMetricPerturbation =
      core.1.metricPerturbation := by
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
    GlobalPhysicalFieldTangent.completeVariation
  simp only [LinearMap.comp_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.coe_add, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.inr_apply, Prod.fst_add, add_zero]
  change core.1.metricPerturbation + 0 + 0 = core.1.metricPerturbation
  simp

@[simp]
theorem diagonalExtendedBulkMinimalPhysicalTangent_gauge
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core).1).independent.gauge =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.1.potential := by
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
    GlobalPhysicalFieldTangent.completeVariation
  simp only [LinearMap.comp_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.coe_add, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.inr_apply, Prod.fst_add, add_zero]
  change (0 : _) +
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.1.potential + 0 =
    globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
      data core.2.1.potential
  simp

private theorem diagonalExtendedBulkMinimalPhysicalTangent_eq_zero_of_components
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis)
    (hMetric : core.1.metricPerturbation = 0)
    (hPotential : core.2.1.potential = 0)
    (hMatter : core.2.2.1 = 0)
    (hLL : core.2.2.2 = 0) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis core = 0 := by
  unfold diagonalExtendedBulkMinimalPhysicalTangentLinearMap
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
  simp only [LinearMap.comp_apply, LinearMap.fst_apply]
  apply Subtype.ext
  change
    (diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis core).1.1 = 0
  have hDiffeomorphism :
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
        configuration core.1).1 = 0 := by
    change globalMetricPerturbationMinimalPhysicalTangentLinearMap period
      hPeriod configuration.physical core.1.metricPerturbation = 0
    rw [hMetric, map_zero]
  have hAbelian :
      (globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
        configuration data core.2.1).1 = 0 := by
    change globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
      hPeriod data core.2.1.potential = 0
    rw [hPotential, map_zero]
  have hAssembly :
      diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
          configuration data analysis core =
        diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
              configuration core.1 +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
              configuration data core.2.1 +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            core.2.2.1 +
      extendedLLGaugeFixedTangentLinearMap period hPeriod configuration analysis
          core.2.2.2 :=
    rfl
  rw [hAssembly]
  simp only [Prod.fst_add]
  rw [hDiffeomorphism, hAbelian, hMatter, hLL]
  simp

/-- The completed physical features vanish on a smooth core exactly when the
canonical minimal physical tangent vanishes. -/
theorem globalCandidateAMinimalPhysicalFeatureProjection_smooth_eq_zero_iff
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis core) = 0 ↔
      core ∈ globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis := by
  constructor
  · intro hFeature
    rw [globalCandidateAMinimalPhysicalFeatureProjection_smooth] at hFeature
    have hPlusGraph :
        globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
            (Metric period hPeriod configuration data .plus)
            (core.1.metricPerturbation .plus) = 0 := by
      exact congrArg (fun value => value.1.1) hFeature
    have hMinusGraph :
        globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
            (Metric period hPeriod configuration data .minus)
            (core.1.metricPerturbation .minus) = 0 := by
      exact congrArg (fun value => value.1.2) hFeature
    have hPlus : core.1.metricPerturbation .plus = 0 := by
      apply globalGeneralMetricDeDonderPairingSmoothEmbedding_injective period
        hPeriod (Metric period hPeriod configuration data .plus)
      simpa only [map_zero] using hPlusGraph
    have hMinus : core.1.metricPerturbation .minus = 0 := by
      apply globalGeneralMetricDeDonderPairingSmoothEmbedding_injective period
        hPeriod (Metric period hPeriod configuration data .minus)
      simpa only [map_zero] using hMinusGraph
    have hMetric : core.1.metricPerturbation = 0 := by
      funext sector
      cases sector with
      | plus => exact hPlus
      | minus => exact hMinus
    have hPotentialGraph :
        globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod
            (Metric period hPeriod configuration data) core.2.1.potential = 0 := by
      exact congrArg (fun value => value.2.1) hFeature
    have hPotential : core.2.1.potential = 0 := by
      have hPotentialGraph' :
          globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod
              (Metric period hPeriod configuration data) core.2.1.potential =
            globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod
              (Metric period hPeriod configuration data) 0 := by
        simpa only [map_zero] using hPotentialGraph
      apply globalPairedAbelianLorenzSmoothEmbedding_injective period hPeriod
        (Metric period hPeriod configuration data)
      apply Subtype.ext
      change
        globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod
            (Metric period hPeriod configuration data) core.2.1.potential =
          globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod
            (Metric period hPeriod configuration data) 0
      exact hPotentialGraph'
    have hMatterGraph :
        programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared core.2.2.1 = 0 := by
      exact congrArg (fun value => value.2.2.1) hFeature
    have hMatter : core.2.2.1 = 0 := by
      have hMatterGraph' :
          programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared core.2.2.1 =
            programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared 0 := by
        simpa only [map_zero] using hMatterGraph
      apply programPPrimitiveSpinCMatterGraphFiniteLinearMap_injective period
        hPeriod couplings.matterMassSquared
      change
        programPPrimitiveSpinCMatterGraphFinite period hPeriod
            couplings.matterMassSquared core.2.2.1 =
          programPPrimitiveSpinCMatterGraphFinite period hPeriod
            couplings.matterMassSquared 0
      change
        programPPrimitiveSpinCMatterGraphFinite period hPeriod
            couplings.matterMassSquared core.2.2.1 =
          programPPrimitiveSpinCMatterGraphFinite period hPeriod
            couplings.matterMassSquared 0 at hMatterGraph'
      exact hMatterGraph'
    have hLLGraph :
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            core.2.2.2 = 0 := by
      exact congrArg (fun value => value.2.2.2) hFeature
    have hLL : core.2.2.2 = 0 := by
      apply globalCandidateAFullLLSmoothEmbedding_injective period hPeriod data
        analysis
      simpa only [map_zero] using hLLGraph
    apply LinearMap.mem_ker.mpr
    exact diagonalExtendedBulkMinimalPhysicalTangent_eq_zero_of_components
      period hPeriod configuration data analysis core hMetric hPotential
        hMatter hLL
  · intro hCore
    have hTangent :
        diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core = 0 :=
      LinearMap.mem_ker.mp hCore
    have hMetricRecovery :=
      diagonalExtendedBulkMinimalPhysicalTangent_metric period hPeriod
        configuration data analysis core
    rw [hTangent] at hMetricRecovery
    change (0 : GlobalMetricPerturbationPair period hPeriod) =
      core.1.metricPerturbation at hMetricRecovery
    have hMetric : core.1.metricPerturbation = 0 := hMetricRecovery.symm
    have hGaugeRecovery :=
      diagonalExtendedBulkMinimalPhysicalTangent_gauge period hPeriod
        configuration data analysis core
    rw [hTangent] at hGaugeRecovery
    change (0 : GaugeVariationPair period hPeriod) =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.1.potential at hGaugeRecovery
    have hPotential : core.2.1.potential = 0 := by
      apply globalCandidateAPairedGaugePotentialCoefficientLinearMap_injective
        period hPeriod data
      simpa only [map_zero] using hGaugeRecovery.symm
    have hMatterRecovery :=
      diagonalExtendedBulkMinimalPhysicalTangent_matter period hPeriod
        configuration data analysis core
    rw [hTangent] at hMatterRecovery
    change (0 : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        core.2.2.1 at hMatterRecovery
    have hMatter : core.2.2.1 = 0 := by
      have hMatterMap :
          programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap period
              hPeriod core.2.2.1 = 0 := by
        change
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              core.2.2.1 = 0
        exact hMatterRecovery.symm
      apply
        programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap_injective
          period hPeriod
      simpa only [map_zero] using hMatterMap
    have hLLRecovery :=
      diagonalExtendedBulkMinimalPhysicalTangent_fullLL period hPeriod
        configuration data analysis core
    rw [hTangent] at hLLRecovery
    change (0 : GlobalFullLLSmooth period hPeriod analysis) = core.2.2.2
      at hLLRecovery
    have hLL : core.2.2.2 = 0 := hLLRecovery.symm
    rw [globalCandidateAMinimalPhysicalFeatureProjection_smooth, hMetric,
      hPotential, hMatter, hLL]
    simp

/-- Closing the smooth null image introduces no vector detected by any
completed physical feature. -/
theorem globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule_le_feature_ker :
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis ≤
      (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis).ker := by
  unfold globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule
  apply Submodule.topologicalClosure_minimal
  · intro state hState
    rcases hState with ⟨core, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact
      (globalCandidateAMinimalPhysicalFeatureProjection_smooth_eq_zero_iff
        period hPeriod configuration data analysis core).2 core.property
  · exact
      (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis).isClosed_ker

/-- The reduced smooth embedding has exactly the canonical minimal physical
kernel; Hilbert closure creates no additional smooth null directions. -/
theorem globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_ker :
    LinearMap.ker
        (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period
          hPeriod configuration data analysis) =
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis := by
  apply le_antisymm
  · intro core hCore
    have hReduced :
        globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
            configuration data analysis
            (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
              configuration data analysis core) = 0 := by
      exact LinearMap.mem_ker.mp hCore
    have hClosed :
        globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
              configuration data analysis core ∈
            globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period
              hPeriod configuration data analysis := by
      rw [← globalCandidateAMinimalPhysicalHilbertReduction_ker period hPeriod
        configuration data analysis]
      exact LinearMap.mem_ker.mpr hReduced
    have hFeatureKer :=
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule_le_feature_ker
        period hPeriod configuration data analysis hClosed
    exact
      (globalCandidateAMinimalPhysicalFeatureProjection_smooth_eq_zero_iff
        period hPeriod configuration data analysis core).1
          (LinearMap.mem_ker.mp hFeatureKer)
  · intro core hCore
    apply LinearMap.mem_ker.mpr
    exact
      globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_eq_zero_of_mem_kernel
        period hPeriod configuration data analysis core hCore

/-- The canonical quotient smooth core embeds injectively in the reduced
physical Hilbert completion. -/
theorem globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_injective :
    Function.Injective
      (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
        hPeriod configuration data analysis) := by
  apply LinearMap.ker_eq_bot.mp
  unfold globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
  apply Submodule.ker_liftQ_eq_bot
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_ker period
    hPeriod configuration data analysis]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
end JanusFormal

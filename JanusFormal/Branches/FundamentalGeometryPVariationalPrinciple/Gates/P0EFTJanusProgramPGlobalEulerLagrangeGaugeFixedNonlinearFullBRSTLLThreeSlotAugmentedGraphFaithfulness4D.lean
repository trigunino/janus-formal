import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D

/-!
# Faithfulness of the three full-BRST LL augmented graphs

Each pure LL slot reaches the already faithful complete LL smooth graph through
the exact chart-core compatibility.  Hence all three augmented graph maps are
injective.  No ellipticity or Fredholm property is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphFaithfulness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLThreeSlotCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldLLFaithfulness :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section LLFaithfulness

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

local instance fullLLGraphInnerProductSpaceLLFaithfulness :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalFullLLGraphInnerProductSpace period hPeriod data analysis

local instance fullLLGraphCompleteSpaceLLFaithfulness :
    CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis

private def llAuxMetricCore
    (test : GlobalMinimalPhysicalLLAuxMetricTest period hPeriod) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (0, (0, (0, ((test, 0), 0))))

private def llMeasureCore
    (test : GlobalMinimalPhysicalLLMeasureTest period hPeriod) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (0, (0, (0, ((0, test), 0))))

private def llFieldCore
    (test : GlobalMinimalPhysicalLLFieldTest period hPeriod) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (0, (0, (0, ((0, 0),
    LLH1Smooth.ofTest period hPeriod
      (analysis.llH1Data period hPeriod) test))))

private def fullLLSmoothSevenBulkCoordinates
    (smooth : GlobalFullLLSmooth period hPeriod analysis) :
    GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod :=
  (0, (0, (0, (0, (smooth.1.1, (smooth.1.2, smooth.2.toTest))))))

private theorem llProjection_sevenBulkFullLL
    (smooth : GlobalFullLLSmooth period hPeriod analysis) :
    (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).llProjection
        (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
          configuration data analysis chartData
          (fullLLSmoothSevenBulkCoordinates period hPeriod configuration
            analysis smooth)) =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        smooth := by
  let bridge := globalCandidateAMinimalPhysicalQuadraticChartBridge period
    hPeriod configuration data analysis chartData
  let core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis := (0, (0, (0, smooth)))
  have hChartTangent
      (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) :
      globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
          configuration data analysis chartData direction =
        bridge.chartBridge.tangentAnalysis direction := by
    rfl
  let source : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical :=
    (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).symm
      ((globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm
          (fullLLSmoothSevenBulkCoordinates period hPeriod configuration
            analysis smooth),
        0)
  have hSource :
      source = diagonalExtendedBulkMinimalPhysicalTangentLinearMap period
        hPeriod configuration data analysis core := by
    apply Subtype.ext
    simp [source, core, fullLLSmoothSevenBulkCoordinates,
      globalMinimalPhysicalTangentSectorEquiv,
      globalMinimalPhysicalSevenBulkEquiv,
      diagonalExtendedBulkMinimalPhysicalTangentLinearMap,
      diagonalExtendedBulkGaugeFixedTangentLinearMap,
      extendedLLGaugeFixedTangentLinearMap,
      globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap,
      globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap,
      extendedLLMinimalTangentLinearMap,
      fullLLSmoothPhysicalTangentLinearMap,
      fullLLSmoothGeneralMetricLinearMap,
      fullLLSmoothMatterFreeLinearMap,
      fullLLSmoothCompleteLinearMap,
      fullLLSmoothIndependentLinearMap,
      independentCompleteVariationLinearMap,
      independentCompleteVariation,
      zeroSmoothDiagonalMetricVariation]
    constructor
    · apply SmoothDiagonalMetricVariation.ext <;> rfl
    constructor
    · funext sector
      rfl
    constructor
    · funext sector
      apply ContMDiffSection.coe_injective
      rfl
    · funext sector
      apply SmoothSymmetricCovariantTwoTensor.ext
      rfl
  have hDirection :
      globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
          configuration data analysis chartData
          (fullLLSmoothSevenBulkCoordinates period hPeriod configuration
            analysis smooth) =
        bridge.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core) := by
    calc
      _ = globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
          configuration data analysis chartData source := by rfl
      _ = bridge.chartBridge.tangentAnalysis source := hChartTangent source
      _ = _ := congrArg bridge.chartBridge.tangentAnalysis hSource
  rw [hDirection]
  simpa [core] using bridge.llProjection_core core

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_apply_eq_smoothEmbedding
    (test : GlobalMinimalPhysicalLLAuxMetricTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period hPeriod
        configuration data analysis chartData test =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        (llAuxMetricCore period hPeriod configuration analysis test).2.2.2 := by
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap,
    globalCandidateAMinimalPhysicalLLAuxMetricChartDirection,
    globalMinimalPhysicalLLAuxMetricTestInclusion, LinearMap.comp_apply,
    Prod.mk_zero_zero, llAuxMetricCore, fullLLSmoothSevenBulkCoordinates] using
      llProjection_sevenBulkFullLL period hPeriod configuration data analysis
        chartData ((test, 0), 0)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_apply_eq_smoothEmbedding
    (test : GlobalMinimalPhysicalLLMeasureTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period hPeriod
        configuration data analysis chartData test =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        (llMeasureCore period hPeriod configuration analysis test).2.2.2 := by
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap,
    globalCandidateAMinimalPhysicalLLMeasureChartDirection,
    globalMinimalPhysicalLLMeasureTestInclusion, LinearMap.comp_apply,
    Prod.mk_zero_zero, llMeasureCore, fullLLSmoothSevenBulkCoordinates] using
      llProjection_sevenBulkFullLL period hPeriod configuration data analysis
        chartData ((0, test), 0)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_apply_eq_smoothEmbedding
    (test : GlobalMinimalPhysicalLLFieldTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period hPeriod
        configuration data analysis chartData test =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        (llFieldCore period hPeriod configuration analysis test).2.2.2 := by
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap,
    globalCandidateAMinimalPhysicalLLFieldChartDirection,
    globalMinimalPhysicalLLFieldTestInclusion, LinearMap.comp_apply,
    Prod.mk_zero_zero, LLH1Smooth.ofTest, llFieldCore,
    fullLLSmoothSevenBulkCoordinates] using
      llProjection_sevenBulkFullLL period hPeriod configuration data analysis
        chartData
          ((0, 0), LLH1Smooth.ofTest period hPeriod
            (analysis.llH1Data period hPeriod) test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_apply_eq_pureSmoothEmbedding
    (test : GlobalMinimalPhysicalLLAuxMetricTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period hPeriod
        configuration data analysis chartData test =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        ((test, 0), 0) := by
  simpa [llAuxMetricCore] using
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_apply_eq_smoothEmbedding
      period hPeriod configuration data analysis chartData test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_apply_eq_pureSmoothEmbedding
    (test : GlobalMinimalPhysicalLLMeasureTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period hPeriod
        configuration data analysis chartData test =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        ((0, test), 0) := by
  simpa [llMeasureCore] using
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_apply_eq_smoothEmbedding
      period hPeriod configuration data analysis chartData test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_apply_eq_pureSmoothEmbedding
    (test : GlobalMinimalPhysicalLLFieldTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period hPeriod
        configuration data analysis chartData test =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        ((0, 0), LLH1Smooth.ofTest period hPeriod
          (analysis.llH1Data period hPeriod) test) := by
  simpa [llFieldCore] using
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_apply_eq_smoothEmbedding
      period hPeriod configuration data analysis chartData test

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period
        hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  have hSmooth :
      (llAuxMetricCore period hPeriod configuration analysis first).2.2.2 =
        (llAuxMetricCore period hPeriod configuration analysis second).2.2.2 := by
    apply globalCandidateAFullLLSmoothEmbedding_injective period hPeriod data
      analysis
    rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_apply_eq_smoothEmbedding,
      ← globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_apply_eq_smoothEmbedding]
    exact hEqual
  exact congrArg (fun smooth => smooth.1.1) hSmooth

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period
        hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  have hSmooth :
      (llMeasureCore period hPeriod configuration analysis first).2.2.2 =
        (llMeasureCore period hPeriod configuration analysis second).2.2.2 := by
    apply globalCandidateAFullLLSmoothEmbedding_injective period hPeriod data
      analysis
    rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_apply_eq_smoothEmbedding,
      ← globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_apply_eq_smoothEmbedding]
    exact hEqual
  exact congrArg (fun smooth => smooth.1.2) hSmooth

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period hPeriod
        configuration data analysis chartData) := by
  intro first second hEqual
  have hSmooth :
      (llFieldCore period hPeriod configuration analysis first).2.2.2 =
        (llFieldCore period hPeriod configuration analysis second).2.2.2 := by
    apply globalCandidateAFullLLSmoothEmbedding_injective period hPeriod data
      analysis
    rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_apply_eq_smoothEmbedding,
      ← globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_apply_eq_smoothEmbedding]
    exact hEqual
  exact congrArg (fun smooth => smooth.2.toTest) hSmooth

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphLinearMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_injective
      period hPeriod configuration data analysis chartData
  simpa [stateDependentAugmentedGraphLinearMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData]
    using congrArg WithLp.fst hEqual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphLinearMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) := by
  intro first second hEqual
  apply globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_injective
    period hPeriod configuration data analysis chartData
  simpa [stateDependentAugmentedGraphLinearMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData]
    using congrArg WithLp.fst hEqual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphLinearMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) := by
  intro first second hEqual
  apply globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_injective
    period hPeriod configuration data analysis chartData
  simpa [stateDependentAugmentedGraphLinearMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData]
    using congrArg WithLp.fst hEqual

/-- Gate 264: all three LL augmented graph coordinates are faithful. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_three_slot_augmented_graph_faithfulness_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
        (stateDependentAugmentedGraphLinearMap
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
            period hPeriod configuration data analysis chartData state)) ∧
      Function.Injective
        (stateDependentAugmentedGraphLinearMap
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
            period hPeriod configuration data analysis chartData state)) ∧
        Function.Injective
          (stateDependentAugmentedGraphLinearMap
            (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
              period hPeriod configuration data analysis chartData state)) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state⟩

end LLFaithfulness
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphFaithfulness4D
end JanusFormal

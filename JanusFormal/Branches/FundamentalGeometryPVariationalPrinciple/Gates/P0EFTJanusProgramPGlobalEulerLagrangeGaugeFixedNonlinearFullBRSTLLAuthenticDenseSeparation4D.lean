import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFaithfulResidualSystemCapstone4D

/-!
# Dense separation of the authentic full-BRST LL residual

The three pure LL block covectors jointly test the whole dense smooth core of
the complete LL graph.  Their simultaneous vanishing is therefore equivalent
to vanishing of the authentic complete LL Riesz residual.  Cross-block
remainders are deliberately excluded from this statement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLAuthenticDenseSeparation4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLThreeSlotCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphFaithfulness4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldLLDenseSeparation :
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

section DenseSeparation

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

private abbrev PhysicalPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
    configuration data analysis chartData state

/-- The three pure LL base maps add to the canonical dense smooth embedding. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotBaseMap_sum_eq_smoothEmbedding
    (smooth : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period
          hPeriod configuration data analysis chartData smooth.1.1 +
        globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period
          hPeriod configuration data analysis chartData smooth.1.2 +
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period hPeriod
          configuration data analysis chartData smooth.2.toTest =
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          smooth := by
  have hAux :
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period
          hPeriod configuration data analysis chartData smooth.1.1 =
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          ((smooth.1.1, 0), 0) := by
    simpa using
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap_apply_eq_pureSmoothEmbedding
        period hPeriod configuration data analysis chartData smooth.1.1
  have hMeasure :
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period
          hPeriod configuration data analysis chartData smooth.1.2 =
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          ((0, smooth.1.2), 0) := by
    simpa using
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap_apply_eq_pureSmoothEmbedding
        period hPeriod configuration data analysis chartData smooth.1.2
  have hField :
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period hPeriod
          configuration data analysis chartData smooth.2.toTest =
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          ((0, 0), LLH1Smooth.ofTest period hPeriod
            (analysis.llH1Data period hPeriod) smooth.2.toTest) := by
    simpa using
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap_apply_eq_pureSmoothEmbedding
        period hPeriod configuration data analysis chartData smooth.2.toTest
  rw [hAux, hMeasure, hField]
  rw [← (globalCandidateAFullLLSmoothEmbedding period hPeriod data
    analysis).map_add, ← (globalCandidateAFullLLSmoothEmbedding period hPeriod
      data analysis).map_add]
  congr 1
  apply Prod.ext
  · apply Prod.ext <;> simp
  · apply LLH1Smooth.ext
    simp [LLH1Smooth.ofTest]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLThreeBlockEulerCovectors_eq_zero_iff_authenticRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) = 0 ∧
      globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) = 0 ∧
        globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) = 0) ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  constructor
  · rintro ⟨hAux, hMeasure, hField⟩
    let functional :
        GlobalFullLLGraphHilbert period hPeriod data analysis →ₗ[Real] Real :=
      (globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period
          hPeriod configuration data analysis chartData state)).toLinearMap
    have hAuxBase
        (test : GlobalMinimalPhysicalLLAuxMetricTest period hPeriod) :
        functional
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap
            period hPeriod configuration data analysis chartData test) = 0 := by
      have hApply := DFunLike.congr_fun hAux test
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBlockEulerCovector_eq_baseCovector]
        at hApply
      simpa only [functional, LinearMap.comp_apply, LinearMap.zero_apply] using
        hApply
    have hMeasureBase
        (test : GlobalMinimalPhysicalLLMeasureTest period hPeriod) :
        functional
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap
            period hPeriod configuration data analysis chartData test) = 0 := by
      have hApply := DFunLike.congr_fun hMeasure test
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBlockEulerCovector_eq_baseCovector]
        at hApply
      simpa only [functional, LinearMap.comp_apply, LinearMap.zero_apply] using
        hApply
    have hFieldBase
        (test : GlobalMinimalPhysicalLLFieldTest period hPeriod) :
        functional
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period
            hPeriod configuration data analysis chartData test) = 0 := by
      have hApply := DFunLike.congr_fun hField test
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBlockEulerCovector_eq_baseCovector]
        at hApply
      simpa only [functional, LinearMap.comp_apply, LinearMap.zero_apply] using
        hApply
    refine
      (@DenseRange.eq_zero_of_inner_left
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        (GlobalFullLLSmooth period hPeriod analysis) Real inferInstance
        inferInstance
        (@globalFullLLGraphInnerProductSpace period hPeriod
          configuration.physical couplings NonNullFace NullFace inferInstance
          inferInstance data analysis) _ _
        (globalCandidateAFullLLSmoothEmbedding_denseRange period hPeriod data
          analysis) ?_)
    intro smooth
    rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing]
    change functional
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        smooth) = 0
    rw [← globalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotBaseMap_sum_eq_smoothEmbedding]
    rw [functional.map_add, functional.map_add, hAuxBase, hMeasureBase,
      hFieldBase]
    simp
  · intro hResidual
    constructor
    · rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBlockEulerCovector_eq_baseCovector]
      apply LinearMap.ext
      intro test
      change globalCandidateAFullLLGraphForm period hPeriod data analysis
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period
            hPeriod configuration data analysis chartData state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period
            hPeriod configuration data analysis chartData test) = 0
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing,
        hResidual]
      exact @inner_zero_left Real
        (GlobalFullLLGraphHilbert period hPeriod data analysis) inferInstance _
        (@globalFullLLGraphInnerProductSpace period hPeriod
          configuration.physical couplings NonNullFace NullFace inferInstance
          inferInstance data analysis) _
    constructor
    · rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBlockEulerCovector_eq_baseCovector]
      apply LinearMap.ext
      intro test
      change globalCandidateAFullLLGraphForm period hPeriod data analysis
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period
            hPeriod configuration data analysis chartData state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period
            hPeriod configuration data analysis chartData test) = 0
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing,
        hResidual]
      exact @inner_zero_left Real
        (GlobalFullLLGraphHilbert period hPeriod data analysis) inferInstance _
        (@globalFullLLGraphInnerProductSpace period hPeriod
          configuration.physical couplings NonNullFace NullFace inferInstance
          inferInstance data analysis) _
    · rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBlockEulerCovector_eq_baseCovector]
      apply LinearMap.ext
      intro test
      change globalCandidateAFullLLGraphForm period hPeriod data analysis
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period
            hPeriod configuration data analysis chartData state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period
            hPeriod configuration data analysis chartData test) = 0
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing,
        hResidual]
      exact @inner_zero_left Real
        (GlobalFullLLGraphHilbert period hPeriod data analysis) inferInstance _
        (@globalFullLLGraphInnerProductSpace period hPeriod
          configuration.physical couplings NonNullFace NullFace inferInstance
          inferInstance data analysis) _

/-- Gate 267: the three authentic LL block equations jointly separate the
complete LL graph Riesz residual. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_authentic_dense_separation_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) = 0 ∧
      globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) = 0 ∧
        globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) = 0) ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLThreeBlockEulerCovectors_eq_zero_iff_authenticRieszResidual
    period hPeriod configuration data analysis chartData state

end DenseSeparation
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLAuthenticDenseSeparation4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotEuler4D

/-!
# Augmented graph-Riesz residuals of the three full-BRST LL equations

Each LL slot retains the authentic complete LL graph form as its Hilbert
coordinate and its exact physical cross-block as a scalar graph coordinate.
No separate vanishing of either contribution is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D

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
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLGraphRieszResidualBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLThreeSlotCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotEuler4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldLLAugmentedResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceLLAugmentedResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldLLAugmentedResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceLLAugmentedResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceLLAugmentedResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section LLThreeSlotAugmentedResidual

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

local instance fullLLGraphInnerProductSpaceLLAugmentedResidual
    {baseConfiguration : GlobalFieldConfiguration period hPeriod}
    {baseCouplings : GlobalCandidateAActionCouplings}
    {BaseNonNullFace BaseNullFace : Type*}
    [Fintype BaseNonNullFace] [Fintype BaseNullFace]
    (baseData : GlobalCandidateAActionData period hPeriod baseConfiguration
      baseCouplings BaseNonNullFace BaseNullFace)
    (baseAnalysis : GlobalAnalysisData period hPeriod baseConfiguration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod baseData baseAnalysis) :=
  globalFullLLGraphInnerProductSpace period hPeriod baseData baseAnalysis

local instance fullLLGraphCompleteSpaceLLAugmentedResidual
    {baseConfiguration : GlobalFieldConfiguration period hPeriod}
    {baseCouplings : GlobalCandidateAActionCouplings}
    {BaseNonNullFace BaseNullFace : Type*}
    [Fintype BaseNonNullFace] [Fintype BaseNullFace]
    (baseData : GlobalCandidateAActionData period hPeriod baseConfiguration
      baseCouplings BaseNonNullFace BaseNullFace)
    (baseAnalysis : GlobalAnalysisData period hPeriod baseConfiguration) :
    CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod baseData baseAnalysis) :=
  globalCandidateAFullLLGraphCompleteSpace period hPeriod baseData baseAnalysis

/-- Pure auxiliary-metric LL tests mapped into the complete LL graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
      configuration data analysis chartData).llProjection.toLinearMap.comp
    (globalCandidateAMinimalPhysicalLLAuxMetricChartDirection period hPeriod
      configuration data analysis chartData)

/-- Pure measure LL tests mapped into the complete LL graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
      configuration data analysis chartData).llProjection.toLinearMap.comp
    (globalCandidateAMinimalPhysicalLLMeasureChartDirection period hPeriod
      configuration data analysis chartData)

/-- Pure LL-field tests mapped into the complete LL graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
      configuration data analysis chartData).llProjection.toLinearMap.comp
    (globalCandidateAMinimalPhysicalLLFieldChartDirection period hPeriod
      configuration data analysis chartData)

/-- Complete LL graph point underlying all three slot equations. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
    configuration data analysis chartData).llProjection
      (PhysicalPoint period hPeriod configuration data analysis chartData state)

/-- Authentic complete LL graph residual shared by all three slots. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalFullLLGraphHilbert period hPeriod data analysis :=
  globalCandidateAFullLLGraphRieszResidual period hPeriod data analysis
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
      configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
          configuration data analysis chartData state) test =
      inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
          period hPeriod configuration data analysis chartData state) test := by
  simpa only [
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual,
    globalCandidateAFullLLGraphRieszResidualPairing] using
    globalCandidateAFullLLGraphForm_eq_rieszResidualPairing period hPeriod data
      analysis
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
        configuration data analysis chartData state) test

/-- Augmented graph data for the coupled LL auxiliary-metric equation. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalLLAuxMetricTest period hPeriod)
      (Base := GlobalFullLLGraphHilbert period hPeriod data analysis) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period hPeriod
      configuration data analysis chartData
  remainder :=
    globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt period
      hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  baseCovector :=
    globalCandidateAFullLLGraphForm period hPeriod data analysis
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
        configuration data analysis chartData state)

/-- Augmented graph data for the coupled LL measure equation. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalLLMeasureTest period hPeriod)
      (Base := GlobalFullLLGraphHilbert period hPeriod data analysis) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period hPeriod
      configuration data analysis chartData
  remainder :=
    globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt period
      hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  baseCovector :=
    globalCandidateAFullLLGraphForm period hPeriod data analysis
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
        configuration data analysis chartData state)

/-- Augmented graph data for the coupled LL-field equation. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalLLFieldTest period hPeriod)
      (Base := GlobalFullLLGraphHilbert period hPeriod data analysis) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period hPeriod
      configuration data analysis chartData
  remainder :=
    globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt period
      hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  baseCovector :=
    globalCandidateAFullLLGraphForm period hPeriod data analysis
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
        configuration data analysis chartData state)

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert
    (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert
    (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert
    (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData period
      hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual
    (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual
    (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual
    (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData period
      hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBlockEulerCovector_eq_baseCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) =
      (globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
          configuration data analysis chartData state)).toLinearMap.comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap period
          hPeriod configuration data analysis chartData) := by
  apply LinearMap.ext
  intro test
  unfold globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBaseMap
    globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint
  rw [globalCandidateAMinimalPhysicalLLBlockEulerCovector_eq_graph]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBlockEulerCovector_eq_baseCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) =
      (globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
          configuration data analysis chartData state)).toLinearMap.comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap period
          hPeriod configuration data analysis chartData) := by
  apply LinearMap.ext
  intro test
  unfold globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBaseMap
    globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint
  rw [globalCandidateAMinimalPhysicalLLBlockEulerCovector_eq_graph]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBlockEulerCovector_eq_baseCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) =
      (globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint period hPeriod
          configuration data analysis chartData state)).toLinearMap.comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap period
          hPeriod configuration data analysis chartData) := by
  apply LinearMap.ext
  intro test
  unfold globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBaseMap
    globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPoint
  rw [globalCandidateAMinimalPhysicalLLBlockEulerCovector_eq_graph]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_augmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector period
        hPeriod configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricBlockEulerCovector_eq_baseCovector]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_augmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector period
        hPeriod configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureBlockEulerCovector_eq_baseCovector]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_augmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector period
        hPeriod configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldBlockEulerCovector_eq_baseCovector]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
  constructor
  · intro hEuler
    apply
      (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
        (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector
            period hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_augmentedTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_augmentedTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_zero_iff_augmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
  constructor
  · intro hEuler
    apply
      (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
        (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
          period hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector
            period hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_augmentedTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_augmentedTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_zero_iff_augmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
  constructor
  · intro hEuler
    apply
      (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
        (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
          period hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector
            period hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_augmentedTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_augmentedTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := GlobalFullLLGraphHilbert period hPeriod data analysis)
          (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_llThreeSlotAugmentedGraphResidual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
            period hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
          period hPeriod configuration data analysis chartData state = 0 := by
  have hEuler :=
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_llThreeSlotEuler_eq_zero
      period hPeriod configuration data analysis chartData state hCritical
  constructor
  · apply
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp
    rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq]
    exact hEuler.1
  · constructor
    · apply
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_zero_iff_augmentedGraphResidual
          period hPeriod configuration data analysis chartData state).mp
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq]
      exact hEuler.2.1
    · apply
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_zero_iff_augmentedGraphResidual
          period hPeriod configuration data analysis chartData state).mp
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq]
      exact hEuler.2.2

/-- Gate 254: all three coupled full-BRST LL equations have exact separating
augmented graph-Riesz residuals over the authentic complete LL graph. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_three_slot_augmented_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector period
            hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector period
          hPeriod configuration data analysis chartData state = 0) ↔
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
            period hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
              period hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
            period hPeriod configuration data analysis chartData state = 0) := by
  constructor
  · rintro ⟨hAux, hMeasure, hField⟩
    exact ⟨
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp hAux,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp hMeasure,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp hField⟩
  · rintro ⟨hAux, hMeasure, hField⟩
    exact ⟨
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hAux,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hMeasure,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hField⟩

end LLThreeSlotAugmentedResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D

/-!
# Fixed-carrier base regularity for the three full-BRST LL coordinates

The common complete LL base residual is a continuous-linear function of the
full-BRST chart point.  Its adjoints along the three fixed carrier inclusions
give the exact smooth Riesz representatives of the three restricted base
covectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotBaseRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

attribute [local instance 10001]
  llAuxMetricFixedNormedAddCommGroup
  llAuxMetricFixedInnerProductSpace
  llAuxMetricFixedNormedSpace
  llAuxMetricFixedModule
  llMeasureFixedNormedAddCommGroup
  llMeasureFixedInnerProductSpace
  llMeasureFixedNormedSpace
  llMeasureFixedModule
  llFieldFixedNormedAddCommGroup
  llFieldFixedInnerProductSpace
  llFieldFixedNormedSpace
  llFieldFixedModule
attribute [local instance 10002]
  llAuxMetricFixedSeminormedAddCommGroup
  llAuxMetricFixedAddCommGroup
  llAuxMetricFixedTopologicalSpace
  llMeasureFixedSeminormedAddCommGroup
  llMeasureFixedAddCommGroup
  llMeasureFixedTopologicalSpace
  llFieldFixedSeminormedAddCommGroup
  llFieldFixedAddCommGroup
  llFieldFixedTopologicalSpace
attribute [local instance 10003]
  llAuxMetricFixedPseudoMetricSpace
  llAuxMetricFixedUniformSpace
  llMeasureFixedPseudoMetricSpace
  llMeasureFixedUniformSpace
  llFieldFixedPseudoMetricSpace
  llFieldFixedUniformSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section LLBaseRegularity

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
    (measure := measure) configuration data analysis chartData

private abbrev LLCommonAmbient :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
    hPeriod configuration data analysis

private abbrev LLAuxMetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev LLMeasureHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev LLFieldHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev LLAuxMetricInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedInclusionCLM
    period hPeriod configuration data analysis chartData

private abbrev LLMeasureInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedInclusionCLM period
    hPeriod configuration data analysis chartData

private abbrev LLFieldInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedInclusionCLM period
    hPeriod configuration data analysis chartData

private abbrev RegularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData

private abbrev RegularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedSpace period hPeriod configuration data analysis
    chartData

local instance (priority := 12000) regularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

local instance (priority := 12000) regularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedSpace period hPeriod configuration data analysis
    chartData

local instance llCommonAmbientInnerProductSpace :
    InnerProductSpace Real
      (LLCommonAmbient period hPeriod configuration data analysis) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
    period hPeriod configuration data analysis

local instance llCommonAmbientCompleteSpace :
    CompleteSpace
      (LLCommonAmbient period hPeriod configuration data analysis) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
    period hPeriod configuration data analysis

local instance llAuxMetricHilbertCompleteSpace :
    CompleteSpace
      (LLAuxMetricHilbert period hPeriod configuration data analysis
        chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedCompleteSpace
    period hPeriod configuration data analysis chartData

local instance llMeasureHilbertCompleteSpace :
    CompleteSpace
      (LLMeasureHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedCompleteSpace period
    hPeriod configuration data analysis chartData

local instance llFieldHilbertCompleteSpace :
    CompleteSpace
      (LLFieldHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedCompleteSpace period
    hPeriod configuration data analysis chartData

private abbrev RegularityContDiff
    {Target : Type*}
    [NormedAddCommGroup Target] [NormedSpace Real Target]
    (map : FullChart period hPeriod configuration data analysis chartData →
      Target) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    Target inferInstance inferInstance ∞ map

/-- The common LL graph point as a continuous linear map of the full-BRST
chart coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPointCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      LLCommonAmbient period hPeriod configuration data analysis :=
  (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
      configuration data analysis chartData).llProjection.comp
    ((globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
        period hPeriod configuration data analysis chartData).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
        period hPeriod configuration data analysis chartData))

/-- Common authentic LL base residual as a continuous linear operator. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      LLCommonAmbient period hPeriod configuration data analysis :=
  (globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphPointCLM period hPeriod
      configuration data analysis chartData)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM_apply
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM period
        hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
        period hPeriod configuration data analysis chartData state :=
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual_contDiff :
    RegularityContDiff period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
        period hPeriod configuration data analysis chartData) := by
  have hFormula :=
    @ContinuousLinearMap.contDiff Real
      (FullChart period hPeriod configuration data analysis chartData)
      (LLCommonAmbient period hPeriod configuration data analysis)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
        period hPeriod configuration data analysis chartData)
  convert hFormula using 1
  funext state
  rfl

/-- Restricted auxiliary-metric base representative. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      LLAuxMetricHilbert period hPeriod configuration data analysis chartData :=
  ((@ContinuousLinearMap.adjoint Real
      (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
      (LLCommonAmbient period hPeriod configuration data analysis)
      _ _ _
      (llAuxMetricFixedInnerProductSpace period hPeriod configuration data
        analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
        period hPeriod configuration data analysis)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedCompleteSpace
        period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
        period hPeriod configuration data analysis))
    (LLAuxMetricInclusion period hPeriod configuration data analysis chartData)
    ).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
        period hPeriod configuration data analysis chartData)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLAuxMetricHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszCLM
    period hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLAuxMetricHilbert period hPeriod configuration data analysis
      chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData state) test =
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
        period hPeriod configuration data analysis chartData state).baseCovector
        (LLAuxMetricInclusion period hPeriod configuration data analysis
          chartData test) := by
  calc
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
          period hPeriod configuration data analysis chartData state)
        (LLAuxMetricInclusion period hPeriod configuration data analysis
          chartData test) :=
      @ContinuousLinearMap.adjoint_inner_left Real
        (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
        (LLCommonAmbient period hPeriod configuration data analysis)
        _ _ _
        (llAuxMetricFixedInnerProductSpace period hPeriod configuration data
          analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
          period hPeriod configuration data analysis)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedCompleteSpace
          period hPeriod configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
          period hPeriod configuration data analysis)
        (LLAuxMetricInclusion period hPeriod configuration data analysis
          chartData) test
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
          period hPeriod configuration data analysis chartData state)
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
          period hPeriod configuration data analysis chartData state)
        (LLAuxMetricInclusion period hPeriod configuration data analysis
          chartData test) := by
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM_apply]
    _ = _ :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing
        period hPeriod configuration data analysis chartData state
          (LLAuxMetricInclusion period hPeriod configuration data analysis
            chartData test)).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative_contDiff :
    RegularityContDiff period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative
        period hPeriod configuration data analysis chartData) := by
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (llAuxMetricFixedNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (llAuxMetricFixedNormedSpace period hPeriod configuration data analysis
      chartData)
    ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszCLM
      period hPeriod configuration data analysis chartData)

/-- Restricted measure base representative. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      LLMeasureHilbert period hPeriod configuration data analysis chartData :=
  ((@ContinuousLinearMap.adjoint Real
      (LLMeasureHilbert period hPeriod configuration data analysis chartData)
      (LLCommonAmbient period hPeriod configuration data analysis)
      _ _ _
      (llMeasureFixedInnerProductSpace period hPeriod configuration data
        analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
        period hPeriod configuration data analysis)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedCompleteSpace
        period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
        period hPeriod configuration data analysis))
    (LLMeasureInclusion period hPeriod configuration data analysis chartData)
    ).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
        period hPeriod configuration data analysis chartData)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLMeasureHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszCLM period
    hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLMeasureHilbert period hPeriod configuration data analysis
      chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData state) test =
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
        period hPeriod configuration data analysis chartData state).baseCovector
        (LLMeasureInclusion period hPeriod configuration data analysis chartData
          test) := by
  calc
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
          period hPeriod configuration data analysis chartData state)
        (LLMeasureInclusion period hPeriod configuration data analysis chartData
          test) :=
      @ContinuousLinearMap.adjoint_inner_left Real
        (LLMeasureHilbert period hPeriod configuration data analysis chartData)
        (LLCommonAmbient period hPeriod configuration data analysis)
        _ _ _
        (llMeasureFixedInnerProductSpace period hPeriod configuration data
          analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
          period hPeriod configuration data analysis)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedCompleteSpace
          period hPeriod configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
          period hPeriod configuration data analysis)
        (LLMeasureInclusion period hPeriod configuration data analysis chartData)
        test
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
          period hPeriod configuration data analysis chartData state)
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
          period hPeriod configuration data analysis chartData state)
        (LLMeasureInclusion period hPeriod configuration data analysis chartData
          test) := by
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM_apply]
    _ = _ :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing
        period hPeriod configuration data analysis chartData state
          (LLMeasureInclusion period hPeriod configuration data analysis
            chartData test)).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative_contDiff :
    RegularityContDiff period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative
        period hPeriod configuration data analysis chartData) := by
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (LLMeasureHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (llMeasureFixedNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (llMeasureFixedNormedSpace period hPeriod configuration data analysis
      chartData)
    ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszCLM
      period hPeriod configuration data analysis chartData)

/-- Restricted field base representative. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      LLFieldHilbert period hPeriod configuration data analysis chartData :=
  ((@ContinuousLinearMap.adjoint Real
      (LLFieldHilbert period hPeriod configuration data analysis chartData)
      (LLCommonAmbient period hPeriod configuration data analysis)
      _ _ _
      (llFieldFixedInnerProductSpace period hPeriod configuration data analysis
        chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
        period hPeriod configuration data analysis)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedCompleteSpace
        period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
        period hPeriod configuration data analysis))
    (LLFieldInclusion period hPeriod configuration data analysis chartData)
    ).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
        period hPeriod configuration data analysis chartData)

def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative
    (state : FullChart period hPeriod configuration data analysis chartData) :
    LLFieldHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszCLM period
    hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : LLFieldHilbert period hPeriod configuration data analysis
      chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData state) test =
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
        period hPeriod configuration data analysis chartData state).baseCovector
        (LLFieldInclusion period hPeriod configuration data analysis chartData
          test) := by
  calc
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
          period hPeriod configuration data analysis chartData state)
        (LLFieldInclusion period hPeriod configuration data analysis chartData
          test) :=
      @ContinuousLinearMap.adjoint_inner_left Real
        (LLFieldHilbert period hPeriod configuration data analysis chartData)
        (LLCommonAmbient period hPeriod configuration data analysis)
        _ _ _
        (llFieldFixedInnerProductSpace period hPeriod configuration data
          analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
          period hPeriod configuration data analysis)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedCompleteSpace
          period hPeriod configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientCompleteSpace
          period hPeriod configuration data analysis)
        (LLFieldInclusion period hPeriod configuration data analysis chartData)
        test
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM
          period hPeriod configuration data analysis chartData state)
    _ = inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
          period hPeriod configuration data analysis chartData state)
        (LLFieldInclusion period hPeriod configuration data analysis chartData
          test) := by
      rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedBaseRieszCLM_apply]
    _ = _ :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLGraphForm_eq_authenticRieszPairing
        period hPeriod configuration data analysis chartData state
          (LLFieldInclusion period hPeriod configuration data analysis chartData
            test)).symm

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative_contDiff :
    RegularityContDiff period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative
        period hPeriod configuration data analysis chartData) := by
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (LLFieldHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (llFieldFixedNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (llFieldFixedNormedSpace period hPeriod configuration data analysis
      chartData)
    ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszCLM period
      hPeriod configuration data analysis chartData)

/-- Gate 311: the common authentic LL base residual and all three of its fixed
carrier restrictions are globally smooth. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_three_slot_base_regularity_gate :
    RegularityContDiff period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual
          period hPeriod configuration data analysis chartData) ∧
      RegularityContDiff period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData) ∧
      RegularityContDiff period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData) ∧
      RegularityContDiff period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuthenticRieszResidual_contDiff
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData⟩

end LLBaseRegularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotBaseRegularity4D
end JanusFormal

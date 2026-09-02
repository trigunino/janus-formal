import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D

/-!
# Canonical fixed-carrier regularity of the metric BRST base

The authentic diagonal diffeomorphism-BRST Riesz residual is a composition of
existing continuous linear maps. Restricting its covector to the fixed metric
carrier and applying Riesz gives a canonical globally smooth representative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricBaseRegularity4D

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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGraphResidualRegularity4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricFixedCarrier4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

attribute [local instance 10001]
  metricFixedNormedAddCommGroup
  metricFixedInnerProductSpace
  metricFixedNormedSpace
  metricFixedModule
attribute [local instance 10002]
  metricFixedSeminormedAddCommGroup
  metricFixedAddCommGroup
  metricFixedTopologicalSpace
attribute [local instance 10003]
  metricFixedPseudoMetricSpace
  metricFixedUniformSpace

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

section MetricBase

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

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev MetricAmbient :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period hPeriod
    configuration data

private abbrev MetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period hPeriod
    configuration data

private abbrev MetricInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedInclusionCLM period hPeriod
    configuration data

@[implicit_reducible]
local instance (priority := 12000) regularityMetricAmbientNormedAddCommGroup :
    NormedAddCommGroup (MetricAmbient period hPeriod configuration data) :=
  diagonalGraphNormedAddCommGroupValue period hPeriod
    (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 12000) regularityMetricAmbientNormedSpace :
    NormedSpace Real (MetricAmbient period hPeriod configuration data) :=
  diagonalGraphNormedSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

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

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedSpace period hPeriod configuration data analysis
    chartData

local instance metricHilbertCompleteSpace :
    CompleteSpace (MetricHilbert period hPeriod configuration data) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedCompleteSpace period
    hPeriod configuration data

private def restrictedMetricBaseRieszCLM
    (Subspace : Type*) [subspaceGroup : NormedAddCommGroup Subspace]
    [subspaceInner : InnerProductSpace Real Subspace]
    [subspaceComplete : CompleteSpace Subspace]
    (inclusion : Subspace →L[Real]
      MetricAmbient period hPeriod configuration data) :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      Subspace :=
  ((InnerProductSpace.toDual Real Subspace).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((inclusion.precomp Real).comp
      ((globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings (BaseMetric period hPeriod configuration data)).comp
        (fullDiffeomorphismBRSTPointCLM period hPeriod configuration data analysis
          chartData)))

/-- Canonical Riesz representative of the authentic base covector on the
fixed metric carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      MetricHilbert period hPeriod configuration data :=
  restrictedMetricBaseRieszCLM period hPeriod configuration data analysis
    chartData (MetricHilbert period hPeriod configuration data)
    (MetricInclusion period hPeriod configuration data)

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MetricHilbert period hPeriod configuration data :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszCLM period
    hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : MetricHilbert period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData state) test =
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData period
        hPeriod configuration data analysis chartData state).baseCovector
        (MetricInclusion period hPeriod configuration data test) := by
  change inner Real
      ((InnerProductSpace.toDual Real
        (MetricHilbert period hPeriod configuration data)).symm
        (((MetricInclusion period hPeriod configuration data).precomp Real).comp
          ((globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
            couplings (BaseMetric period hPeriod configuration data)).comp
            (fullDiffeomorphismBRSTPointCLM period hPeriod configuration data
              analysis chartData)) state)) test = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative
        period hPeriod configuration data analysis chartData) := by
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (MetricHilbert period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszCLM period
      hPeriod configuration data analysis chartData)

/-- Gate 300: the authentic metric BRST base has a canonical globally smooth
fixed-carrier Riesz representative. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_base_regularity_gate :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative
        period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative_contDiff
    period hPeriod configuration data analysis chartData

end MetricBase
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricBaseRegularity4D
end JanusFormal

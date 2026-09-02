import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D

/-!
# Faithfulness of the full-BRST metric augmented graph

The authentic diagonal diffeomorphism graph coordinate already used by the
metric residual is injective on pure metric tests. Consequently the complete
augmented coordinate, including its scalar remainder, is injective as well.
This adds no local tensor PDE, ellipticity or Fredholm claim.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphFaithfulness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

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

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap
        period hPeriod configuration data) := by
  intro first second hEqual
  have hState :=
    globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
      period hPeriod
      (BaseMetric period hPeriod configuration data) hEqual
  have hMetric := congrArg
    GlobalCandidateADiagonalDiffeomorphismBRSTState.metricPerturbation hState
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricGaugeFreeLinearMap] using
      hMetric

def diagonalDiffeomorphismAugmentedGraphCoordinate
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (Test : Type*) [AddCommGroup Test] [Module Real Test]
    (graphData : DiagonalDiffeomorphismAugmentedGraphRieszData period hPeriod
      metric Test) :
    Test → WithLp 2
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric × Real) :=
  fun test => WithLp.toLp 2
    (graphData.baseMap test, graphData.remainder test)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphCoordinate_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (diagonalDiffeomorphismAugmentedGraphCoordinate period hPeriod
        (BaseMetric period hPeriod configuration data)
        (GlobalMinimalPhysicalMetricTest period hPeriod)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) := by
  intro first second hEqual
  apply globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismGraphBaseMap_injective period hPeriod configuration data
  simpa [diagonalDiffeomorphismAugmentedGraphCoordinate,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData] using
      congrArg WithLp.fst hEqual


/-- Gate 259: the metric augmented graph retains a faithful Hilbert
coordinate on pure metric tests. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_augmented_graph_faithfulness_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (diagonalDiffeomorphismAugmentedGraphCoordinate period hPeriod
        (BaseMetric period hPeriod configuration data)
        (GlobalMinimalPhysicalMetricTest period hPeriod)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphCoordinate_injective
    period hPeriod configuration data analysis chartData state

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphFaithfulness4D
end JanusFormal

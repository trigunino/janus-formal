import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingFourRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalResidualRegularityFromData4D

/-!
# Three remaining regularity obligations after normal Robin-cross data

Physical-ghost, potential, SpinC, metric, and normal regularity discharge five
coordinates of the complete fixed residual, leaving exactly the three LL
hypotheses.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeAndPhysicalGhostPotentialSpinCMetricNormalData4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedResidualTargetNormedSpace4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalResidualRegularityFromData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingFourAndPhysicalGhostPotentialSpinCMetricRemainderData4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

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

section RemainingThree

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

/-- The three LL coordinate regularity obligations left after the normal
coordinate. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D :
    Prop where
  llAuxMetric : LLCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualLLAuxMetric period hPeriod configuration data analysis
      chartData)
  llMeasure : LLCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualLLMeasure period hPeriod configuration data analysis
      chartData)
  llField : LLCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualLLField period hPeriod configuration data analysis
      chartData)

/-- The regularity data packages plus the remaining three LL coordinate
hypotheses imply smoothness of the complete residual. -/
theorem fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialSpinCMetricNormalData_and_remaining_three
    (physicalGhostRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (potentialRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (spinCRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (metricRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (normalRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) := by
  apply
    fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialSpinCMetricRemainderData_and_remaining_four
      period hPeriod configuration data analysis chartData
      physicalGhostRegularity potentialRegularity spinCRegularity metricRegularity
  exact
    { normal :=
        fixedNormedResidualNormal_contDiff_of_robinCrossRegularityData period
          hPeriod configuration data analysis chartData normalRegularity
      llAuxMetric := remaining.llAuxMetric
      llMeasure := remaining.llMeasure
      llField := remaining.llField }

/-- Gate 308: physical-ghost, potential, SpinC, metric, and normal regularity
reduce the complete residual frontier to the three LL coordinates. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_normed_residual_remaining_three_and_physicalGhost_potential_spinC_metric_normal_data_gate
    (physicalGhostRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (potentialRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (spinCRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (metricRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (normalRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) :=
  fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialSpinCMetricNormalData_and_remaining_three
    period hPeriod configuration data analysis chartData physicalGhostRegularity
    potentialRegularity spinCRegularity metricRegularity normalRegularity remaining

end RemainingThree
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeAndPhysicalGhostPotentialSpinCMetricNormalData4D
end JanusFormal

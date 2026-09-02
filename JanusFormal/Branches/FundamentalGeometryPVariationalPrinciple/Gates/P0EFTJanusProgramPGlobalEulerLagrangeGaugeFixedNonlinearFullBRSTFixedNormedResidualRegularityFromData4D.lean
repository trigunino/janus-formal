import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotResidualRegularityFromData4D

/-!
# Regularity of the complete fixed normed full-BRST residual from data

The six fixed-carrier regularity packages discharge every remaining coordinate
of the fourteen-coordinate residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityFromData4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeAndPhysicalGhostPotentialSpinCMetricNormalData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotResidualRegularityFromData4D

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

section RegularityFromData

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

/-- The six analytic data packages imply global `C∞` regularity of the
complete fixed normed residual. -/
theorem fixedNormedEulerResidualOperator_contDiff_of_all_remainderRegularityData
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
    (llRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) := by
  apply
    fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialSpinCMetricNormalData_and_remaining_three
      period hPeriod configuration data analysis chartData physicalGhostRegularity
      potentialRegularity spinCRegularity metricRegularity normalRegularity
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D_of_llThreeSlotRemainderRegularityData
      period hPeriod configuration data analysis chartData llRegularity

/-- Gate 314: the six fixed-carrier analytic packages discharge all fourteen
coordinates of the complete fixed normed residual. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_normed_residual_regularity_from_data_gate
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
    (llRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) :=
  fixedNormedEulerResidualOperator_contDiff_of_all_remainderRegularityData period
    hPeriod configuration data analysis chartData physicalGhostRegularity
    potentialRegularity spinCRegularity metricRegularity normalRegularity
    llRegularity

end RegularityFromData
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityFromData4D
end JanusFormal

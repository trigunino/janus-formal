import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixAndPhysicalGhostPotentialData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulResidualRegularityFromData4D

/-!
# Five remaining regularity obligations after ghost, potential, and SpinC data

Physical-ghost and potential Euler regularity together with smooth SpinC
cross-block remainder data discharge three coordinates of the complete fixed
residual, leaving exactly the metric, normal, and three LL hypotheses.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingFiveAndPhysicalGhostPotentialSpinCRemainderData4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulResidualRegularityFromData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixAndPhysicalGhostPotentialData4D

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

section RemainingFive

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

/-- The five coordinate regularity obligations other than physical ghost,
potential, and SpinC. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingFiveCoordinateContDiff4D :
    Prop where
  metric : MetricCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualMetric period hPeriod configuration data analysis
      chartData)
  normal : CoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualNormal period hPeriod configuration data analysis
      chartData)
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

/-- The three fixed-carrier data packages plus the other five coordinate
hypotheses imply smoothness of the complete residual. -/
theorem fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialSpinCRemainderData_and_remaining_five
    (physicalGhostRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (potentialRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (spinCRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingFiveCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) := by
  apply
    fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialData_and_remaining_six
      period hPeriod configuration data analysis chartData
      physicalGhostRegularity potentialRegularity
  exact
    { metric := remaining.metric
      normal := remaining.normal
      llAuxMetric := remaining.llAuxMetric
      llMeasure := remaining.llMeasure
      llField := remaining.llField
      spinC :=
        fixedNormedResidualSpinC_contDiff_of_remainderRegularityData period
          hPeriod configuration data analysis chartData spinCRegularity }

/-- Gate 297: physical-ghost, potential, and SpinC remainder regularity reduce
the complete residual frontier to the metric, normal, and three LL coordinates. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_normed_residual_remaining_five_and_physicalGhost_potential_spinC_remainder_data_gate
    (physicalGhostRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (potentialRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (spinCRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingFiveCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) :=
  fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialSpinCRemainderData_and_remaining_five
    period hPeriod configuration data analysis chartData physicalGhostRegularity
    potentialRegularity spinCRegularity remaining

end RemainingFive
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingFiveAndPhysicalGhostPotentialSpinCRemainderData4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenAndPhysicalGhostData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialResidualRegularityFromData4D

/-!
# Six remaining regularity obligations after ghost and potential data

Fixed-carrier physical-ghost and potential Euler regularity discharge their two
coordinates, leaving exactly six hypotheses sufficient for global smoothness of
the complete fixed-normed residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixAndPhysicalGhostPotentialData4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialResidualRegularityFromData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenAndPhysicalGhostData4D

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

section RemainingSix

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

/-- The six coordinate regularity obligations other than physical ghost and
potential. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixCoordinateContDiff4D :
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
  spinC : CoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualSpinC period hPeriod configuration data analysis
      chartData)

/-- Fixed-carrier physical-ghost and potential Euler regularity plus the other
six coordinate hypotheses imply smoothness of the complete residual. -/
theorem fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialData_and_remaining_six
    (physicalGhostRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (potentialRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) := by
  apply
    fixedNormedEulerResidualOperator_contDiff_of_physicalGhostData_and_remaining_seven
      period hPeriod configuration data analysis chartData
      physicalGhostRegularity
  exact
    { metric := remaining.metric
      normal := remaining.normal
      llAuxMetric := remaining.llAuxMetric
      llMeasure := remaining.llMeasure
      llField := remaining.llField
      spinC := remaining.spinC
      potential :=
        fixedNormedResidualPotential_contDiff_of_eulerRegularityData period
          hPeriod configuration data analysis chartData potentialRegularity }

/-- Gate 291: physical-ghost and potential Euler regularity reduce the complete
residual frontier to the other six coordinate regularity obligations. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_normed_residual_remaining_six_and_physicalGhost_potential_data_gate
    (physicalGhostRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (potentialRegularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) :=
  fixedNormedEulerResidualOperator_contDiff_of_physicalGhostPotentialData_and_remaining_six
    period hPeriod configuration data analysis chartData physicalGhostRegularity
    potentialRegularity remaining

end RemainingSix
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSixAndPhysicalGhostPotentialData4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostResidualRegularityFromL2Data4D

/-!
# Seven remaining regularity obligations after physical-ghost data

Fixed-carrier physical-ghost Euler regularity discharges the physical-ghost
coordinate, leaving exactly seven coordinate hypotheses sufficient for the
complete fixed-normed residual to be globally smooth.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenAndPhysicalGhostData4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingEightRegularity4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostResidualRegularityFromL2Data4D

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

section RemainingSeven

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

/-- The seven coordinate regularity obligations other than physical ghost. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenCoordinateContDiff4D :
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
  potential : PotentialCoordinateContDiff period hPeriod configuration data
    analysis chartData
    (fixedNormedResidualPotential period hPeriod configuration data analysis
      chartData)

/-- Fixed-carrier physical-ghost Euler regularity plus the other seven
coordinate hypotheses imply smoothness of the complete residual. -/
theorem fixedNormedEulerResidualOperator_contDiff_of_physicalGhostData_and_remaining_seven
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) := by
  apply (fixedNormedEulerResidualOperator_contDiff_iff_remaining_eight period
    hPeriod configuration data analysis chartData).mpr
  exact
    { metric := remaining.metric
      normal := remaining.normal
      physicalGhost :=
        fixedNormedResidualPhysicalGhost_contDiff_of_l2EulerRegularityData
          period hPeriod configuration data analysis chartData regularity
      llAuxMetric := remaining.llAuxMetric
      llMeasure := remaining.llMeasure
      llField := remaining.llField
      spinC := remaining.spinC
      potential := remaining.potential }

/-- Gate 286: physical-ghost Euler regularity reduces the complete residual
frontier to the other seven coordinate regularity obligations. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_normed_residual_remaining_seven_and_physicalGhost_data_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (remaining :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenCoordinateContDiff4D
        period hPeriod configuration data analysis chartData) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
        period hPeriod configuration data analysis chartData) :=
  fixedNormedEulerResidualOperator_contDiff_of_physicalGhostData_and_remaining_seven
    period hPeriod configuration data analysis chartData regularity remaining

end RemainingSeven
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingSevenAndPhysicalGhostData4D
end JanusFormal

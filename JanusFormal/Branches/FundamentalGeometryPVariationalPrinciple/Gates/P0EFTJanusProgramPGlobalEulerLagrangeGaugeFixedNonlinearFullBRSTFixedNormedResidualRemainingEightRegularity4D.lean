import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGraphResidualRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostResidualRegularity4D

/-!
# The eight remaining regularity obligations for the full-BRST residual

Six of the fourteen fixed residual coordinates are already globally smooth.
Consequently, smoothness of the complete normed residual is equivalent to the
eight genuinely state-dependent graph/Riesz coordinate obligations below.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingEightRegularity4D

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

section RemainingEight

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

/-- The eight state-dependent coordinate regularity obligations left after
Gates 276--278. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingEightCoordinateContDiff4D :
    Prop where
  metric : MetricCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualMetric period hPeriod configuration data analysis
      chartData)
  normal : CoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualNormal period hPeriod configuration data analysis
      chartData)
  physicalGhost : CoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualPhysicalGhost period hPeriod configuration data analysis
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

/-- Complete residual smoothness is exactly the conjunction of the eight
state-dependent coordinate obligations that remain open. -/
theorem fixedNormedEulerResidualOperator_contDiff_iff_remaining_eight :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
        chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
          period hPeriod configuration data analysis chartData) ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingEightCoordinateContDiff4D
        period hPeriod configuration data analysis chartData := by
  constructor
  · intro h
    have coordinates :=
      (fixedNormedEulerResidualOperator_contDiff_iff_coordinates period hPeriod
        configuration data analysis chartData).mp h
    exact
      { metric := coordinates.metric
        normal := coordinates.normal
        physicalGhost := coordinates.physicalGhost
        llAuxMetric := coordinates.llAuxMetric
        llMeasure := coordinates.llMeasure
        llField := coordinates.llField
        spinC := coordinates.spinC
        potential := coordinates.potential }
  · intro remaining
    apply (fixedNormedEulerResidualOperator_contDiff_iff_coordinates period
      hPeriod configuration data analysis chartData).mpr
    exact
      { metric := remaining.metric
        normal := remaining.normal
        physicalGhost := remaining.physicalGhost
        llAuxMetric := remaining.llAuxMetric
        llMeasure := remaining.llMeasure
        llField := remaining.llField
        spinC := remaining.spinC
        diffeomorphismGhost :=
          P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGraphResidualRegularity4D.fixedNormedResidualDiffeomorphismGhost_contDiff
            period hPeriod configuration data analysis chartData
        diffeomorphismAntighost :=
          P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGraphResidualRegularity4D.fixedNormedResidualDiffeomorphismAntighost_contDiff
            period hPeriod configuration data analysis chartData
        diffeomorphismNakanishiLautrup :=
          P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGraphResidualRegularity4D.fixedNormedResidualDiffeomorphismNakanishiLautrup_contDiff
            period hPeriod configuration data analysis chartData
        potential := remaining.potential
        abelianGhost :=
          P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostResidualRegularity4D.fixedNormedResidualAbelianGhost_contDiff
            period hPeriod configuration data analysis chartData
        abelianAntighost := fixedNormedResidualAbelianAntighost_contDiff period
          hPeriod configuration data analysis chartData
        abelianNakanishiLautrup :=
          fixedNormedResidualAbelianNakanishiLautrup_contDiff period hPeriod
            configuration data analysis chartData }

/-- Gate 279: the complete normed residual has only eight remaining `C∞`
coordinate obligations. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_normed_residual_remaining_eight_regularity_gate :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
        chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
          period hPeriod configuration data analysis chartData) ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingEightCoordinateContDiff4D
        period hPeriod configuration data analysis chartData :=
  fixedNormedEulerResidualOperator_contDiff_iff_remaining_eight period hPeriod
    configuration data analysis chartData

end RemainingEight
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingEightRegularity4D
end JanusFormal

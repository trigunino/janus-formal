import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertAtlasResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

/-!
# Local equations of the reduced nonlinear Hilbert residual atlas

The descended atlas equation recovers the genuine local Euler equation, weak
eight-sector system and any separating componentwise PDE realization in every
member chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertAtlasPDE4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (atlas :
      GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas
        period hPeriod (measure := measure) configuration data analysis)

/-- Atlas criticality is the genuine local Euler equation in every member. -/
theorem GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas.isEulerCritical_iff_chart_localEuler
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ atlas.carrier)
    (index : atlas.Index) :
    atlas.IsEulerCritical period hPeriod state ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (atlas.chartData index))
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.reducedChart index) state) = 0 := by
  rw [GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas.IsEulerCritical,
    atlas.residual_eq_chart period hPeriod state hState index]
  change GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
      hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state ↔ _
  exact
    globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_localEuler
      period hPeriod configuration data analysis (atlas.chartData index)
        (atlas.reducedChart index) state

/-- Atlas criticality recovers the weak eight-sector equations in every
admissible member chart. -/
theorem GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas.isEulerCritical_iff_chart_weakEightSectorSystem
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ atlas.carrier)
    (index : atlas.Index) :
    atlas.IsEulerCritical period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis (atlas.chartData index)
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis (atlas.chartData index)
              (atlas.reducedChart index) state) :=
  (GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas.isEulerCritical_iff_chart_localEuler
    period hPeriod atlas state hState index).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
        period hPeriod configuration data analysis (atlas.chartData index) _
          (atlas.transition state hState atlas.referenceIndex index).second_mem_domain)

/-- Atlas criticality is any supplied separating eight-component strong PDE
system for the selected member chart. -/
theorem GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas.isEulerCritical_iff_chart_componentwiseStrongPDE
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ atlas.carrier)
    (index : atlas.Index)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis (atlas.chartData index)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.reducedChart index) state)) :
    atlas.IsEulerCritical period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis (atlas.chartData index)
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis (atlas.chartData index)
              (atlas.reducedChart index) state) pdeData :=
  (GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas.isEulerCritical_iff_chart_localEuler
    period hPeriod atlas state hState index).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
        period hPeriod configuration data analysis (atlas.chartData index) _
          pdeData)

/-- The descended action is the genuine covariant action in every member
chart. -/
theorem GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertResidualAtlas.action_eq_chart_covariant
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ atlas.carrier)
    (index : atlas.Index) :
    atlas.action period hPeriod state =
      globalCandidateACovariantAction period hPeriod
        ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (atlas.chartData index)).family.datumAt
            (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
              hPeriod configuration data analysis (atlas.chartData index)
                (atlas.reducedChart index) state)
            (atlas.transition state hState atlas.referenceIndex index).second_mem_domain).2
        measure := by
  rw [atlas.action_eq_chart period hPeriod state hState index]
  exact globalCandidateAMinimalPhysicalReducedHilbertAction_eq_covariant_of_mem
    period hPeriod configuration data analysis (atlas.chartData index)
      (atlas.reducedChart index) state
      (atlas.transition state hState atlas.referenceIndex index).second_mem_domain

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertAtlasPDE4D
end JanusFormal

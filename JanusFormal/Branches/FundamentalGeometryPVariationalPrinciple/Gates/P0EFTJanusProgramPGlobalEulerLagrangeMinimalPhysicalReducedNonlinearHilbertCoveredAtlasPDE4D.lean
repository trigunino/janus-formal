import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

/-!
# Local equations of the covered reduced nonlinear Hilbert atlas

On every member domain containing a covered state, the descended equation is
the genuine weak eight-sector system and any separating componentwise strong
PDE realization.  The descended action is the genuine covariant action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlasPDE4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlas4D
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
      GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas period
        hPeriod (measure := measure) configuration data analysis)

/-- Covered-atlas criticality recovers the weak eight-sector system in every
member domain containing the state. -/
theorem GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas.isEulerCritical_iff_chart_weakEightSectorSystem
    (state : atlas.carrier) (index : atlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData index)).family.domain) :
    atlas.IsEulerCritical period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis (atlas.chartData index)
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis (atlas.chartData index)
              (atlas.reducedChart index) state.1) :=
  (atlas.isEulerCritical_iff_chart_localEuler period hPeriod state index
    hPoint).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
        period hPeriod configuration data analysis (atlas.chartData index) _
          hPoint)

/-- Covered-atlas criticality is any supplied separating eight-component
strong PDE system in a member domain containing the state. -/
theorem GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas.isEulerCritical_iff_chart_componentwiseStrongPDE
    (state : atlas.carrier) (index : atlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData index)).family.domain)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis (atlas.chartData index)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis (atlas.chartData index)
            (atlas.reducedChart index) state.1)) :
    atlas.IsEulerCritical period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis (atlas.chartData index)
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis (atlas.chartData index)
              (atlas.reducedChart index) state.1) pdeData :=
  (atlas.isEulerCritical_iff_chart_localEuler period hPeriod state index
    hPoint).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
        period hPeriod configuration data analysis (atlas.chartData index) _
          pdeData)

/-- The descended action is the genuine covariant action in every member
domain containing the covered state. -/
theorem GlobalCandidateAMinimalPhysicalReducedNonlinearHilbertCoveredAtlas.action_eq_chart_covariant
    (state : atlas.carrier) (index : atlas.Index)
    (hPoint : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
        hPeriod configuration data analysis (atlas.chartData index)
          (atlas.reducedChart index) state.1 ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis (atlas.chartData index)).family.domain) :
    atlas.action period hPeriod state =
      globalCandidateACovariantAction period hPeriod
        ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis (atlas.chartData index)).family.datumAt
            (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
              hPeriod configuration data analysis (atlas.chartData index)
                (atlas.reducedChart index) state.1) hPoint).2 measure := by
  rw [atlas.action_eq_chart period hPeriod state index hPoint]
  exact globalCandidateAMinimalPhysicalReducedHilbertAction_eq_covariant_of_mem
    period hPeriod configuration data analysis (atlas.chartData index)
      (atlas.reducedChart index) state.1 hPoint

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertCoveredAtlasPDE4D
end JanusFormal

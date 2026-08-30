import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertChartTransition4D

/-!
# Atlas descent of the nonlinear Hilbert Euler residual

A compatible family of bounded chart realizations defines one nonlinear Riesz
residual, independent of the selected chart on its Hilbert carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

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
open P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertChartTransition4D

universe u v

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

/-- Exact data required to descend the nonlinear Hilbert residual through a
family of local variational charts. -/
structure GlobalCandidateANonlinearHilbertResidualAtlas
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  Index : Type v
  chart : Index → GlobalCandidateALocalVariationalChart.{u} period hPeriod
    couplings NonNullFace NullFace measure
  basePoint : (index : Index) → (chart index).Model
  chartRealization : (index : Index) →
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      (chart index).Model
  carrier : Set
    (CommonAugmentedHilbert period hPeriod configuration data analysis)
  referenceIndex : Index
  transition : ∀ (state : CommonAugmentedHilbert period hPeriod configuration
      data analysis), state ∈ carrier → ∀ first second : Index,
    GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      (chart first) (chart second)
      (globalCandidateANonlinearHilbertChartPoint period hPeriod configuration
        data analysis (chart first) (basePoint first) (chartRealization first)
          state)
      (globalCandidateANonlinearHilbertChartPoint period hPeriod configuration
        data analysis (chart second) (basePoint second) (chartRealization second)
          state)
  derivative_compatible : ∀ (state : CommonAugmentedHilbert period hPeriod
      configuration data analysis) (hState : state ∈ carrier)
      (first second : Index),
    ((transition state hState first second).derivative.toContinuousLinearMap.comp
      (chartRealization first)) = chartRealization second

namespace GlobalCandidateANonlinearHilbertResidualAtlas

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (atlas : GlobalCandidateANonlinearHilbertResidualAtlas period hPeriod
      (measure := measure) configuration data analysis)

/-- Every bounded realization into one local chart gives a genuine singleton
residual atlas on the states mapped into its admissible domain. -/
def singleton
    (chart : GlobalCandidateALocalVariationalChart.{u} period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model) :
    GlobalCandidateANonlinearHilbertResidualAtlas period hPeriod
      (measure := measure) configuration data analysis where
  Index := Unit
  chart := fun _ ↦ chart
  basePoint := fun _ ↦ basePoint
  chartRealization := fun _ ↦ chartRealization
  carrier := {state | globalCandidateANonlinearHilbertChartPoint period hPeriod
    configuration data analysis chart basePoint chartRealization state ∈
      chart.family.domain}
  referenceIndex := ()
  transition := by
    intro state hState first second
    cases first
    cases second
    exact GlobalCandidateALocalVariationalChartTransitionAt.refl period hPeriod
      chart _ hState
  derivative_compatible := by
    intro state hState first second
    cases first
    cases second
    apply ContinuousLinearMap.ext
    intro direction
    rfl

/-- Chart-independent action, defined in the distinguished reference chart. -/
def action :
    CommonAugmentedHilbert period hPeriod configuration data analysis → Real :=
  globalCandidateANonlinearHilbertAction period hPeriod configuration data
    analysis (atlas.chart atlas.referenceIndex)
      (atlas.basePoint atlas.referenceIndex)
      (atlas.chartRealization atlas.referenceIndex)

/-- Chart-independent nonlinear strong Euler residual. -/
noncomputable def residual :
    CommonAugmentedHilbert period hPeriod configuration data analysis →
      CommonAugmentedHilbert period hPeriod configuration data analysis :=
  globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
    data analysis (atlas.chart atlas.referenceIndex)
      (atlas.basePoint atlas.referenceIndex)
      (atlas.chartRealization atlas.referenceIndex)

/-- The descended nonlinear Euler equation. -/
def IsEulerCritical
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    Prop :=
  atlas.residual period hPeriod state = 0

theorem action_eq_chart
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈ atlas.carrier) (index : atlas.Index) :
    atlas.action period hPeriod state =
      globalCandidateANonlinearHilbertAction period hPeriod configuration data
        analysis (atlas.chart index) (atlas.basePoint index)
          (atlas.chartRealization index) state := by
  exact globalCandidateANonlinearHilbertAction_transition period hPeriod
    configuration data analysis (atlas.chart atlas.referenceIndex)
      (atlas.chart index) (atlas.basePoint atlas.referenceIndex)
      (atlas.basePoint index) (atlas.chartRealization atlas.referenceIndex)
      (atlas.chartRealization index) state
      (atlas.transition state hState atlas.referenceIndex index)

theorem residual_eq_chart
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈ atlas.carrier) (index : atlas.Index) :
    atlas.residual period hPeriod state =
      globalCandidateANonlinearHilbertRieszResidual period hPeriod configuration
        data analysis (atlas.chart index) (atlas.basePoint index)
          (atlas.chartRealization index) state := by
  exact globalCandidateANonlinearHilbertRieszResidual_transition period hPeriod
    configuration data analysis (atlas.chart atlas.referenceIndex)
      (atlas.chart index) (atlas.basePoint atlas.referenceIndex)
      (atlas.basePoint index) (atlas.chartRealization atlas.referenceIndex)
      (atlas.chartRealization index) state
      (atlas.transition state hState atlas.referenceIndex index)
      (atlas.derivative_compatible state hState atlas.referenceIndex index)

/-- Criticality of the descended residual is exactly stationarity in any
chart realization. -/
theorem isEulerCritical_iff_chart_fderiv
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈ atlas.carrier) (index : atlas.Index) :
    atlas.IsEulerCritical period hPeriod state ↔
      fderiv Real
        (globalCandidateANonlinearHilbertAction period hPeriod configuration data
          analysis (atlas.chart index) (atlas.basePoint index)
            (atlas.chartRealization index)) state = 0 := by
  rw [IsEulerCritical, atlas.residual_eq_chart period hPeriod state hState index]
  exact (globalCandidateANonlinearHilbertAction_fderiv_eq_zero_iff_rieszResidual
    period hPeriod configuration data analysis (atlas.chart index)
      (atlas.basePoint index) (atlas.chartRealization index) state
      (atlas.transition state hState atlas.referenceIndex index).second_mem_domain).symm

end GlobalCandidateANonlinearHilbertResidualAtlas

end
end P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
end JanusFormal

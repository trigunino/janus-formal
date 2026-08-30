import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalLocalVariationalChart4D

/-!
# Euler--Lagrange transport between local variational charts

This gate proves the coordinate-change law for the derivative of the same
Candidate-A action on an overlap. It is the calculus bridge required before a
chartwise Euler one-form can be promoted to a global atlas object.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D

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

/-- An overlap transition between two local variational charts at specified
points. The local equality says that both coordinate expressions represent the
same physical action. -/
structure GlobalCandidateALocalVariationalChartTransitionAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (first : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (second : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (firstPoint : first.Model) (secondPoint : second.Model) where
  first_mem_domain : firstPoint ∈ first.family.domain
  second_mem_domain : secondPoint ∈ second.family.domain
  toFun : first.Model → second.Model
  derivative : first.Model ≃L[Real] second.Model
  maps_point : toFun firstPoint = secondPoint
  hasFDerivAt : HasFDerivAt toFun derivative.toContinuousLinearMap firstPoint
  action_eventuallyEq :
    globalCandidateALocalActionPullback period hPeriod first =ᶠ[𝓝 firstPoint]
      globalCandidateALocalActionPullback period hPeriod second ∘ toFun

/-- The Euler one-form obeys the exact covector transition law on every valid
overlap. -/
theorem globalCandidateALocalEulerLagrangeOperator_transition
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {first : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {second : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {firstPoint : first.Model} {secondPoint : second.Model}
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second firstPoint secondPoint) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod first firstPoint =
      (globalCandidateALocalEulerLagrangeOperator period hPeriod second secondPoint).comp
        transition.derivative.toContinuousLinearMap := by
  have hSecondAtPoint :=
    globalCandidateALocalAction_hasFDerivAt period hPeriod second secondPoint
      transition.second_mem_domain
  have hSecondAtImage :
      HasFDerivAt
        (globalCandidateALocalActionPullback period hPeriod second)
        (globalCandidateALocalEulerLagrangeOperator period hPeriod second secondPoint)
        (transition.toFun firstPoint) := by
    simpa only [transition.maps_point] using hSecondAtPoint
  have hComposed := hSecondAtImage.comp firstPoint transition.hasFDerivAt
  have hTransported :=
    hComposed.congr_of_eventuallyEq transition.action_eventuallyEq
  have hFirst :=
    globalCandidateALocalAction_hasFDerivAt period hPeriod first firstPoint
      transition.first_mem_domain
  exact hFirst.unique hTransported

/-- Pointwise form of the Euler covector transition law. -/
theorem globalCandidateALocalEulerLagrangeOperator_transition_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {first : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {second : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {firstPoint : first.Model} {secondPoint : second.Model}
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second firstPoint secondPoint)
    (direction : first.Model) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod first firstPoint direction =
      globalCandidateALocalEulerLagrangeOperator period hPeriod second secondPoint
        (transition.derivative direction) := by
  exact congrArg (fun functional => functional direction)
    (globalCandidateALocalEulerLagrangeOperator_transition period hPeriod transition)

/-- Criticality is independent of the chosen local variational chart. -/
theorem globalCandidateALocalEulerLagrangeOperator_eq_zero_iff
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {first : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {second : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {firstPoint : first.Model} {secondPoint : second.Model}
    (transition : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second firstPoint secondPoint) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod first firstPoint = 0 ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod second secondPoint = 0 := by
  have hTransition :=
    globalCandidateALocalEulerLagrangeOperator_transition period hPeriod transition
  constructor
  · intro hFirst
    apply ContinuousLinearMap.ext
    intro direction
    have hAt := congrArg
      (fun functional => functional (transition.derivative.symm direction))
      hTransition
    simpa [hFirst] using hAt.symm
  · intro hSecond
    simp [hTransition, hSecond]

/-- Identity overlap transition. -/
def GlobalCandidateALocalVariationalChartTransitionAt.refl
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      chart chart point point where
  first_mem_domain := hPoint
  second_mem_domain := hPoint
  toFun := id
  derivative := ContinuousLinearEquiv.refl Real chart.Model
  maps_point := rfl
  hasFDerivAt := (ContinuousLinearEquiv.refl Real chart.Model).hasFDerivAt
  action_eventuallyEq := Eventually.of_forall fun _ => rfl

/-- Composition of overlap transitions. -/
def GlobalCandidateALocalVariationalChartTransitionAt.trans
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {first : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {second : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {third : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {firstPoint : first.Model} {secondPoint : second.Model}
    {thirdPoint : third.Model}
    (firstSecond : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first second firstPoint secondPoint)
    (secondThird : GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      second third secondPoint thirdPoint) :
    GlobalCandidateALocalVariationalChartTransitionAt period hPeriod
      first third firstPoint thirdPoint where
  first_mem_domain := firstSecond.first_mem_domain
  second_mem_domain := secondThird.second_mem_domain
  toFun := secondThird.toFun ∘ firstSecond.toFun
  derivative := firstSecond.derivative.trans secondThird.derivative
  maps_point := by
    change secondThird.toFun (firstSecond.toFun firstPoint) = thirdPoint
    rw [firstSecond.maps_point, secondThird.maps_point]
  hasFDerivAt := by
    have hSecondThirdAt :
        HasFDerivAt secondThird.toFun secondThird.derivative.toContinuousLinearMap
          (firstSecond.toFun firstPoint) := by
      rw [firstSecond.maps_point]
      exact secondThird.hasFDerivAt
    simpa using hSecondThirdAt.comp firstPoint firstSecond.hasFDerivAt
  action_eventuallyEq := by
    have hTendsto : Tendsto firstSecond.toFun (𝓝 firstPoint) (𝓝 secondPoint) := by
      have hContinuous := firstSecond.hasFDerivAt.continuousAt
      exact (congrArg 𝓝 firstSecond.maps_point) ▸ hContinuous
    have hSecondThird := hTendsto.eventually secondThird.action_eventuallyEq
    filter_upwards [firstSecond.action_eventuallyEq, hSecondThird] with point
      hFirstSecond hSecondThird
    exact hFirstSecond.trans hSecondThird

end
end P0EFTJanusProgramPGlobalEulerLagrangeChartTransition4D
end JanusFormal

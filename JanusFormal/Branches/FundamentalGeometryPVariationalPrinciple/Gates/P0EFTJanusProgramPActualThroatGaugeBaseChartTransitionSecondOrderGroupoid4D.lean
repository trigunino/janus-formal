import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D

/-!
# Second-order groupoid laws for actual throat base-chart transitions

This gate closes the unit and inverse laws for the genuine extended-chart
transition germs, their Jacobians and their Hessians.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Units -/

/-- A chart transition from a chart to itself is locally the identity. -/
theorem throatGaugeBaseChartTransition_self_eventuallyEq
    (center current : EffectiveThroat period hPeriod)
    (hCenter : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    throatGaugeBaseChartTransition period hPeriod center center
        =ᶠ[𝓝 (extChartAt throatCoverModelWithCorners center current)] id := by
  have hTarget :
      extChartAt throatCoverModelWithCorners center current ∈
        (extChartAt throatCoverModelWithCorners center).target :=
    (extChartAt throatCoverModelWithCorners center).map_source hCenter
  filter_upwards [extChartAt_target_mem_nhds' hTarget] with coordinate hCoordinate
  exact (extChartAt throatCoverModelWithCorners center).right_inv hCoordinate

/-- The Jacobian of a self-transition is the identity. -/
@[simp]
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
    (center current : EffectiveThroat period hPeriod)
    (hCenter : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      center center current hCenter hCenter).firstDerivative =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
  rw [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative]
  simpa using
    (throatGaugeBaseChartTransition_self_eventuallyEq period hPeriod
      center current hCenter).fderiv_eq (𝕜 := Real)

/-- The Hessian of a self-transition vanishes. -/
@[simp]
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
    (center current : EffectiveThroat period hPeriod)
    (hCenter : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      center center current hCenter hCenter).secondDerivative = 0 := by
  rw [throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative]
  have hFirstDerivative :
      fderiv Real
          (throatGaugeBaseChartTransition period hPeriod center center)
          =ᶠ[𝓝 (extChartAt throatCoverModelWithCorners center current)]
        fun _ => ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    filter_upwards [
      (throatGaugeBaseChartTransition_self_eventuallyEq period hPeriod
        center current hCenter).fderiv (𝕜 := Real)] with coordinate hCoordinate
    simpa using hCoordinate
  exact (hFirstDerivative.fderiv_eq (𝕜 := Real)).trans
    (hasFDerivAt_const (𝕜 := Real)
      (x := extChartAt throatCoverModelWithCorners center current)
      (c := ContinuousLinearMap.id Real ThroatCoverCoordinates)).fderiv

/-! ## Inverses -/

/-- Reversing a transition gives its local inverse. -/
theorem throatGaugeBaseChartTransition_inverse_comp_eventuallyEq
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter ∘
      throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
        =ᶠ[𝓝 (extChartAt throatCoverModelWithCorners firstCenter current)] id := by
  exact
    (throatGaugeBaseChartTransition_cocycle_eventuallyEq period hPeriod
      firstCenter secondCenter firstCenter current hFirst hSecond).symm.trans
      (throatGaugeBaseChartTransition_self_eventuallyEq period hPeriod
        firstCenter current hFirst)

/-- The two transition Jacobians are inverse linear maps. -/
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_inverse
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      secondCenter firstCenter current hSecond hFirst).firstDerivative.comp
        (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
          firstCenter secondCenter current hFirst hSecond).firstDerivative =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
  simpa only [
    throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative] using
    (throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
      period hPeriod firstCenter secondCenter firstCenter current
        hFirst hSecond hFirst).symm

/-- The Hessians of mutually inverse transitions satisfy the second-order
inverse chain rule. -/
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_inverse_apply
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      secondCenter firstCenter current hSecond hFirst).secondDerivative
        ((throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
          firstCenter secondCenter current hFirst hSecond).firstDerivative first)
        ((throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
          firstCenter secondCenter current hFirst hSecond).firstDerivative second) +
      (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
        secondCenter firstCenter current hSecond hFirst).firstDerivative
          ((throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
            firstCenter secondCenter current hFirst hSecond).secondDerivative
              first second) = 0 := by
  simpa only [
    throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative,
    zero_apply] using
    (throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
      period hPeriod firstCenter secondCenter firstCenter current
        hFirst hSecond hFirst first second).symm

end
end P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
end JanusFormal

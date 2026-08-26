import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D

/-!
# Second-order cocycle for actual throat base-chart transitions

The genuine extended-chart transitions are packaged as second-order jets at a
common throat point.  On a triple chart overlap their value, Jacobian and
Hessian satisfy the exact composition laws.

The tangent frame is not changed here.  This is base-chart groupoid data, not
yet the combined frame/chart descent of the gauge jet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D

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

/-! ## Transition germs and their jets -/

/-- On a triple overlap, the direct base-chart transition is locally the
composition of the two successive transitions. -/
theorem throatGaugeBaseChartTransition_cocycle_eventuallyEq
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
        =ᶠ[𝓝
          (extChartAt throatCoverModelWithCorners firstCenter current)]
      throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  have hFirstTarget :
      extChartAt throatCoverModelWithCorners firstCenter current ∈
        (extChartAt throatCoverModelWithCorners firstCenter).target :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hInverseContinuous :
      ContinuousAt
        (extChartAt throatCoverModelWithCorners firstCenter).symm
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    continuousAt_extChartAt_symm'' hFirstTarget
  have hSecondPreimage :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          (extChartAt throatCoverModelWithCorners secondCenter).source ∈
        𝓝 (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact extChartAt_source_mem_nhds' hSecond)
  filter_upwards [hSecondPreimage] with coordinate hCoordinate
  simp only [throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hCoordinate]

/-- The genuine transition from one base chart to another, packaged with its
first and symmetric second derivatives at the common point. -/
def throatGaugeBaseChartTransitionSecondOrderJetAt
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    FramedSecondOrderJet ThroatCoverCoordinates ThroatCoverCoordinates :=
  chartwiseSecondOrderJetAt
    (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
    (extChartAt throatCoverModelWithCorners firstCenter current)
    (throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      firstCenter secondCenter current hFirst hSecond)

@[simp]
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_value
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      firstCenter secondCenter current hFirst hSecond).value =
      extChartAt throatCoverModelWithCorners secondCenter current := by
  rw [throatGaugeBaseChartTransitionSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value,
    throatGaugeBaseChartTransition_apply_current period hPeriod
      firstCenter secondCenter current hFirst]

@[simp]
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      firstCenter secondCenter current hFirst hSecond).firstDerivative =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
  rfl

@[simp]
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      firstCenter secondCenter current hFirst hSecond).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter))
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
  rfl

/-! ## Exact second-order cocycle -/

/-- The Jacobian of the direct transition is the composition of the two
successive transition Jacobians. -/
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (hThird : current ∈
      (extChartAt throatCoverModelWithCorners thirdCenter).source) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      firstCenter thirdCenter current hFirst hThird).firstDerivative =
      (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
        secondCenter thirdCenter current hSecond hThird).firstDerivative.comp
          (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
            firstCenter secondCenter current hFirst hSecond).firstDerivative := by
  let firstToSecond :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let secondToThird :=
    throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter
  let firstToThird :=
    throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
  let firstCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter current
  let secondCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter current
  have hFirstToSecond : ContDiffAt Real 2 firstToSecond firstCoordinate := by
    simpa only [firstToSecond, firstCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod firstCenter
        secondCenter current hFirst hSecond
  have hSecondToThird : ContDiffAt Real 2 secondToThird secondCoordinate := by
    simpa only [secondToThird, secondCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod secondCenter
        thirdCenter current hSecond hThird
  have hAt : firstToSecond firstCoordinate = secondCoordinate := by
    simpa only [firstToSecond, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hGerm : firstToThird =ᶠ[𝓝 firstCoordinate]
      secondToThird ∘ firstToSecond := by
    simpa only [firstToThird, secondToThird, firstToSecond, firstCoordinate]
      using throatGaugeBaseChartTransition_cocycle_eventuallyEq period hPeriod
        firstCenter secondCenter thirdCenter current hFirst hSecond
  rw [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative]
  calc
    fderiv Real firstToThird firstCoordinate =
        fderiv Real (secondToThird ∘ firstToSecond) firstCoordinate :=
      hGerm.fderiv_eq
    _ = (fderiv Real secondToThird secondCoordinate).comp
        (fderiv Real firstToSecond firstCoordinate) := by
      rw [fderiv_comp firstCoordinate
        (by simpa only [hAt] using
          hSecondToThird.differentiableAt (by norm_num))
        (hFirstToSecond.differentiableAt (by norm_num)), hAt]

/-- The Hessian of the direct transition is the exact second-order chain-rule
cocycle: transported first Hessian plus the Hessian of the second transition. -/
theorem throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (hThird : current ∈
      (extChartAt throatCoverModelWithCorners thirdCenter).source)
    (first second : ThroatCoverCoordinates) :
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      firstCenter thirdCenter current hFirst hThird).secondDerivative
        first second =
      (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
        secondCenter thirdCenter current hSecond hThird).secondDerivative
          ((throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
            firstCenter secondCenter current hFirst hSecond).firstDerivative first)
          ((throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
            firstCenter secondCenter current hFirst hSecond).firstDerivative second) +
      (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
        secondCenter thirdCenter current hSecond hThird).firstDerivative
          ((throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
            firstCenter secondCenter current hFirst hSecond).secondDerivative
              first second) := by
  let firstToSecond :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let secondToThird :=
    throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter
  let firstToThird :=
    throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
  let firstCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter current
  let secondCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter current
  have hFirstToSecond : ContDiffAt Real 2 firstToSecond firstCoordinate := by
    simpa only [firstToSecond, firstCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod firstCenter
        secondCenter current hFirst hSecond
  have hSecondToThird : ContDiffAt Real 2 secondToThird secondCoordinate := by
    simpa only [secondToThird, secondCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod secondCenter
        thirdCenter current hSecond hThird
  have hAt : firstToSecond firstCoordinate = secondCoordinate := by
    simpa only [firstToSecond, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hSecondToThirdAtFirstToSecond :
      ContDiffAt Real 2 secondToThird (firstToSecond firstCoordinate) := by
    simpa only [hAt] using hSecondToThird
  have hGerm : firstToThird =ᶠ[𝓝 firstCoordinate]
      secondToThird ∘ firstToSecond := by
    simpa only [firstToThird, secondToThird, firstToSecond, firstCoordinate]
      using throatGaugeBaseChartTransition_cocycle_eventuallyEq period hPeriod
        firstCenter secondCenter thirdCenter current hFirst hSecond
  have hSecondDerivative :
      fderiv Real (fderiv Real firstToThird) firstCoordinate =
        fderiv Real (fderiv Real (secondToThird ∘ firstToSecond))
          firstCoordinate :=
    (hGerm.fderiv).fderiv_eq
  rw [throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative]
  rw [show fderiv Real (fderiv Real firstToThird) firstCoordinate
      first second =
    fderiv Real (fderiv Real (secondToThird ∘ firstToSecond))
      firstCoordinate first second by
    exact congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates =>
        derivative first second) hSecondDerivative]
  rw [second_fderiv_comp_apply firstToSecond secondToThird firstCoordinate
    hFirstToSecond hSecondToThirdAtFirstToSecond, hAt]

end
end P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
end JanusFormal

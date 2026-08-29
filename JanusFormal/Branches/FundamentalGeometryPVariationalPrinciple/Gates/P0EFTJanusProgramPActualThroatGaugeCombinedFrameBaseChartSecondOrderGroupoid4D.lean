import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D

/-!
# Combined second-order groupoid laws for throat frame/base-chart transitions

This gate closes the unit and inverse laws for the semidirect transition made
of an extended base-chart change and a varying covector-frame change.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderGroupoid4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderCocycle4D

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

/-! ## Combined units -/

/-- In any chart containing the point, a repeated frame anchor gives the
constant identity covector transition as a germ. -/
theorem throatGaugeCovectorTransitionCenteredChart_self_eventuallyEq
    (anchor center current : EffectiveThroat period hPeriod)
    (hAnchor : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    throatGaugeCovectorTransitionCenteredChart period hPeriod
        anchor anchor center =ᶠ[𝓝
          (extChartAt throatCoverModelWithCorners center current)]
      fun _ => ContinuousLinearMap.id Real
        (FramedCovector ThroatCoverCoordinates) := by
  have hChartInverse : ContinuousAt
      (extChartAt throatCoverModelWithCorners center).symm
      (extChartAt throatCoverModelWithCorners center current) :=
    continuousAt_extChartAt_symm' hChart
  have hFrameEventually :
      (extChartAt throatCoverModelWithCorners center).symm ⁻¹'
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) anchor).baseSet ∈
        𝓝 (extChartAt throatCoverModelWithCorners center current) :=
    hChartInverse.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners center).left_inv hChart]
      exact (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).open_baseSet.mem_nhds hAnchor)
  filter_upwards [hFrameEventually] with coordinate hCoordinate
  have hTangent := throatGaugeTangentTrivializationTransitionAt_self
    period hPeriod anchor
      ((extChartAt throatCoverModelWithCorners center).symm coordinate)
      hCoordinate
  simp only [throatGaugeCovectorTransitionCenteredChart,
    throatGaugeCovectorTrivializationTransitionAt, hTangent]
  apply ContinuousLinearMap.ext
  intro covector
  apply ContinuousLinearMap.ext
  intro vector
  simp

/-- The value of a repeated-frame transition is the identity. -/
@[simp]
theorem throatGaugeCovectorTransitionCenteredChart_self
    (anchor center current : EffectiveThroat period hPeriod)
    (hAnchor : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    throatGaugeCovectorTransitionCenteredChart period hPeriod
        anchor anchor center
        (extChartAt throatCoverModelWithCorners center current) =
      ContinuousLinearMap.id Real
        (FramedCovector ThroatCoverCoordinates) :=
  (throatGaugeCovectorTransitionCenteredChart_self_eventuallyEq
    period hPeriod anchor center current hAnchor hChart).eq_of_nhds

/-- The first derivative of a repeated-frame transition vanishes. -/
@[simp]
theorem throatGaugeCovectorTransitionCenteredChart_self_firstDerivative
    (anchor center current : EffectiveThroat period hPeriod)
    (hAnchor : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          anchor anchor center)
        (extChartAt throatCoverModelWithCorners center current) = 0 := by
  exact
    ((throatGaugeCovectorTransitionCenteredChart_self_eventuallyEq
      period hPeriod anchor center current hAnchor hChart).fderiv_eq
        (𝕜 := Real)).trans
      (hasFDerivAt_const (𝕜 := Real)
        (x := extChartAt throatCoverModelWithCorners center current)
        (c := ContinuousLinearMap.id Real
          (FramedCovector ThroatCoverCoordinates))).fderiv

/-- The second derivative of a repeated-frame transition vanishes. -/
@[simp]
theorem throatGaugeCovectorTransitionCenteredChart_self_secondDerivative
    (anchor center current : EffectiveThroat period hPeriod)
    (hAnchor : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners center).source)
    (second : ThroatCoverCoordinates) :
    fderiv Real
        (fun coordinate =>
          fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              anchor anchor center) coordinate second)
        (extChartAt throatCoverModelWithCorners center current) = 0 := by
  have hFirstDerivative :
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            anchor anchor center) =ᶠ[𝓝
              (extChartAt throatCoverModelWithCorners center current)]
        fun _ => (0 : ThroatCoverCoordinates →L[Real]
          (FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates)) := by
    filter_upwards [
      (throatGaugeCovectorTransitionCenteredChart_self_eventuallyEq
        period hPeriod anchor center current hAnchor hChart).fderiv
          (𝕜 := Real)] with coordinate hCoordinate
    exact hCoordinate.trans
      (hasFDerivAt_const (𝕜 := Real) (x := coordinate)
        (c := ContinuousLinearMap.id Real
          (FramedCovector ThroatCoverCoordinates))).fderiv
  have hApplied :
      (fun coordinate =>
        fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            anchor anchor center) coordinate second) =ᶠ[𝓝
              (extChartAt throatCoverModelWithCorners center current)]
        fun _ => (0 : FramedCovector ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates) := by
    filter_upwards [hFirstDerivative] with coordinate hCoordinate
    simpa only [zero_apply] using congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          (FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates) => derivative second)
      hCoordinate
  exact (hApplied.fderiv_eq (𝕜 := Real)).trans
    (hasFDerivAt_const (𝕜 := Real)
      (x := extChartAt throatCoverModelWithCorners center current)
      (c := (0 : FramedCovector ThroatCoverCoordinates →L[Real]
        FramedCovector ThroatCoverCoordinates))).fderiv

/-- A repeated frame/chart pair is the identity semidirect transition germ. -/
theorem throatGaugeFrameBaseChartTransition_self_eventuallyEq
    (anchor center current : EffectiveThroat period hPeriod)
    (hAnchor : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    (fun coordinate =>
      (throatGaugeBaseChartTransition period hPeriod center center coordinate,
        throatGaugeCovectorTransitionCenteredChart period hPeriod
          anchor anchor center coordinate)) =ᶠ[𝓝
            (extChartAt throatCoverModelWithCorners center current)]
      fun coordinate =>
        (coordinate, ContinuousLinearMap.id Real
          (FramedCovector ThroatCoverCoordinates)) := by
  filter_upwards [
    throatGaugeBaseChartTransition_self_eventuallyEq period hPeriod
      center current hChart,
    throatGaugeCovectorTransitionCenteredChart_self_eventuallyEq
      period hPeriod anchor center current hAnchor hChart] with coordinate
      hBase hFrame
  exact Prod.ext (by simpa using hBase) hFrame

/-! ## Combined inverses -/

/-- Reversing both frame and chart transitions gives the local inverse of the
semidirect transition. -/
theorem throatGaugeFrameBaseChartTransition_inverse_comp_eventuallyEq
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (fun coordinate =>
      (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter coordinate),
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor firstAnchor secondCenter
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter coordinate)).comp
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter coordinate))) =ᶠ[𝓝
              (extChartAt throatCoverModelWithCorners firstCenter current)]
      fun coordinate =>
        (coordinate, ContinuousLinearMap.id Real
          (FramedCovector ThroatCoverCoordinates)) := by
  exact
    (throatGaugeFrameBaseChartTransition_cocycle_eventuallyEq period hPeriod
      firstAnchor secondAnchor firstAnchor firstCenter secondCenter firstCenter
        current ⟨hCurrent.1, hCurrent.2, hCurrent.1⟩ hFirst hSecond).symm.trans
      (throatGaugeFrameBaseChartTransition_self_eventuallyEq period hPeriod
        firstAnchor firstCenter current hCurrent.1 hFirst)

/-- First-order inverse identity for the varying frame transition, including
the Jacobian of the intervening base-chart change. -/
theorem throatGaugeFrameBaseChartTransition_firstDerivative_inverse
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (direction : ThroatCoverCoordinates) :
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
        secondAnchor firstAnchor secondCenter
        (extChartAt throatCoverModelWithCorners secondCenter current)).comp
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current) direction) +
    (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor firstAnchor secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
          direction)).comp
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor firstCenter
        (extChartAt throatCoverModelWithCorners firstCenter current)) = 0 := by
  have hCocycle :=
    throatGaugeFrameBaseChartTransition_firstDerivative_cocycle
      period hPeriod firstAnchor secondAnchor firstAnchor firstCenter
        secondCenter current ⟨hCurrent.1, hCurrent.2, hCurrent.1⟩
          hFirst hSecond direction
  rw [throatGaugeCovectorTransitionCenteredChart_self_firstDerivative
    period hPeriod firstAnchor firstCenter current hCurrent.1 hFirst] at hCocycle
  exact hCocycle.symm

/-- Second-order inverse identity for the varying frame transition.  The five
terms include both derivatives of the frame transition and the Jacobian and
Hessian of the base-chart transition. -/
theorem throatGaugeFrameBaseChartTransition_secondDerivative_inverse_apply
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates)
    (covector : FramedCovector ThroatCoverCoordinates) :
    throatGaugeCovectorTransitionCenteredChart period hPeriod
        secondAnchor firstAnchor secondCenter
        (extChartAt throatCoverModelWithCorners secondCenter current)
      (fderiv Real
        (fun coordinate =>
          fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor firstCenter) coordinate second)
        (extChartAt throatCoverModelWithCorners firstCenter current)
          first covector) +
    fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor firstAnchor secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) first)
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)
          second covector) +
    fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor firstAnchor secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) second)
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)
          first covector) +
    fderiv Real
        (fun coordinate =>
          fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              secondAnchor firstAnchor secondCenter) coordinate
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter)
              (extChartAt throatCoverModelWithCorners firstCenter current)
                second))
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) first)
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor firstCenter
        (extChartAt throatCoverModelWithCorners firstCenter current) covector) +
    fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor firstAnchor secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (fun coordinate =>
            fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter) coordinate second)
          (extChartAt throatCoverModelWithCorners firstCenter current) first)
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor firstCenter
        (extChartAt throatCoverModelWithCorners firstCenter current) covector) = 0 := by
  have hCocycle :=
    throatGaugeFrameBaseChartTransition_secondDerivative_cocycle_apply
      period hPeriod firstAnchor secondAnchor firstAnchor firstCenter
        secondCenter current ⟨hCurrent.1, hCurrent.2, hCurrent.1⟩
          hFirst hSecond first second covector
  rw [throatGaugeCovectorTransitionCenteredChart_self_secondDerivative
    period hPeriod firstAnchor firstCenter current hCurrent.1 hFirst second]
    at hCocycle
  simpa only [zero_apply] using hCocycle.symm

end
end P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderGroupoid4D
end JanusFormal

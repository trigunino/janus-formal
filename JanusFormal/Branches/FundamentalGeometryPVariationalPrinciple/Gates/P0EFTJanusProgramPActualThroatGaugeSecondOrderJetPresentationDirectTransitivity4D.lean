import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

/-!
# Transitivity of direct throat gauge second-jet compatibility

The exact base-chart and varying-frame cocycles compose the value, Jacobian
and Hessian transition laws of arbitrary local second-jet presentations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectTransitivity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set
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
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

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

private theorem fderiv_clm_apply_const_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (field : X → Y →L[Real] Z) (point direction : X) (value : Y)
    (hField : DifferentiableAt Real field point) :
    fderiv Real (fun current ↦ field current value) point direction =
      fderiv Real field point direction value := by
  have hDerivative :=
    fderiv_clm_apply hField (differentiableAt_const (c := value))
  have hApplied := congrArg
    (fun derivative : X →L[Real] Z ↦ derivative direction) hDerivative
  simpa using hApplied

private theorem directFirstTransition_trans
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    (A₁₂ A₂₃ A₁₃ : X →L[Real] X)
    (D₁₂ D₂₃ D₁₃ : V →L[Real] V)
    (E₁₂ E₂₃ E₁₃ : X → V →L[Real] V)
    (p₀ q₀ : V) (p₁ q₁ r₁ : X →L[Real] V)
    (hA : A₁₃ = A₂₃.comp A₁₂)
    (hD : D₁₃ = D₂₃.comp D₁₂)
    (hE : ∀ u, E₁₃ u = D₂₃.comp (E₁₂ u) +
      (E₂₃ (A₁₂ u)).comp D₁₂)
    (h₀ : q₀ = D₁₂ p₀)
    (h₁₂ : ∀ u, q₁ (A₁₂ u) = D₁₂ (p₁ u) + E₁₂ u p₀)
    (h₂₃ : ∀ u, r₁ (A₂₃ u) = D₂₃ (q₁ u) + E₂₃ u q₀)
    (u : X) :
    r₁ (A₁₃ u) = D₁₃ (p₁ u) + E₁₃ u p₀ := by
  rw [hA, ContinuousLinearMap.comp_apply, h₂₃ (A₁₂ u), h₁₂ u,
    h₀, hD, hE u]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    map_add]
  abel

private theorem directSecondTransition_trans
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    (A₁₂ A₂₃ A₁₃ : X →L[Real] X)
    (B₁₂ B₂₃ B₁₃ : X → X → X)
    (D₁₂ D₂₃ D₁₃ : V →L[Real] V)
    (E₁₂ E₂₃ E₁₃ : X → V →L[Real] V)
    (F₁₂ F₂₃ F₁₃ : X → X → V →L[Real] V)
    (p₀ q₀ : V)
    (p₁ q₁ r₁ : X →L[Real] V)
    (p₂ q₂ r₂ : X →L[Real] X →L[Real] V)
    (hA : A₁₃ = A₂₃.comp A₁₂)
    (hB : ∀ u v, B₁₃ u v = B₂₃ (A₁₂ u) (A₁₂ v) + A₂₃ (B₁₂ u v))
    (hD : D₁₃ = D₂₃.comp D₁₂)
    (hE : ∀ u, E₁₃ u = D₂₃.comp (E₁₂ u) +
      (E₂₃ (A₁₂ u)).comp D₁₂)
    (hF : ∀ u v, F₁₃ u v =
      D₂₃.comp (F₁₂ u v) +
      (E₂₃ (A₁₂ u)).comp (E₁₂ v) +
      (E₂₃ (A₁₂ v)).comp (E₁₂ u) +
      (F₂₃ (A₁₂ u) (A₁₂ v)).comp D₁₂ +
      (E₂₃ (B₁₂ u v)).comp D₁₂)
    (h₀ : q₀ = D₁₂ p₀)
    (h₁₂ : ∀ u, q₁ (A₁₂ u) = D₁₂ (p₁ u) + E₁₂ u p₀)
    (h₂₃ : ∀ u, r₁ (A₂₃ u) = D₂₃ (q₁ u) + E₂₃ u q₀)
    (hSecond₁₂ : ∀ u v,
      q₂ (A₁₂ u) (A₁₂ v) + q₁ (B₁₂ u v) =
        D₁₂ (p₂ u v) + E₁₂ u (p₁ v) + E₁₂ v (p₁ u) +
          F₁₂ u v p₀)
    (hSecond₂₃ : ∀ u v,
      r₂ (A₂₃ u) (A₂₃ v) + r₁ (B₂₃ u v) =
        D₂₃ (q₂ u v) + E₂₃ u (q₁ v) + E₂₃ v (q₁ u) +
          F₂₃ u v q₀)
    (u v : X) :
    r₂ (A₁₃ u) (A₁₃ v) + r₁ (B₁₃ u v) =
      D₁₃ (p₂ u v) + E₁₃ u (p₁ v) + E₁₃ v (p₁ u) +
        F₁₃ u v p₀ := by
  rw [hA, hB u v, map_add]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← add_assoc, hSecond₂₃ (A₁₂ u) (A₁₂ v), h₂₃ (B₁₂ u v)]
  calc
    D₂₃ (q₂ (A₁₂ u) (A₁₂ v)) +
          E₂₃ (A₁₂ u) (q₁ (A₁₂ v)) +
          E₂₃ (A₁₂ v) (q₁ (A₁₂ u)) +
          F₂₃ (A₁₂ u) (A₁₂ v) q₀ +
          (D₂₃ (q₁ (B₁₂ u v)) + E₂₃ (B₁₂ u v) q₀) =
        D₂₃ (q₂ (A₁₂ u) (A₁₂ v) + q₁ (B₁₂ u v)) +
          E₂₃ (A₁₂ u) (q₁ (A₁₂ v)) +
          E₂₃ (A₁₂ v) (q₁ (A₁₂ u)) +
          F₂₃ (A₁₂ u) (A₁₂ v) q₀ +
          E₂₃ (B₁₂ u v) q₀ := by
            rw [map_add]
            abel
    _ = D₂₃ (D₁₂ (p₂ u v) + E₁₂ u (p₁ v) +
          E₁₂ v (p₁ u) + F₁₂ u v p₀) +
          E₂₃ (A₁₂ u) (q₁ (A₁₂ v)) +
          E₂₃ (A₁₂ v) (q₁ (A₁₂ u)) +
          F₂₃ (A₁₂ u) (A₁₂ v) q₀ +
          E₂₃ (B₁₂ u v) q₀ := by rw [hSecond₁₂ u v]
    _ = D₁₃ (p₂ u v) + E₁₃ u (p₁ v) + E₁₃ v (p₁ u) +
          F₁₃ u v p₀ := by
            rw [h₁₂ v, h₁₂ u, h₀, hD, hE u, hE v, hF u v]
            simp only [ContinuousLinearMap.comp_apply,
              add_apply, map_add]
            abel

/-! ## Exact transitivity -/

/-- Direct compatibility is transitive already, before taking its generated
equivalence closure. -/
theorem directTransitionCompatible_trans
    {current : EffectiveThroat period hPeriod}
    {first second third :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current}
    (hFirstSecond :
      DirectTransitionCompatible period hPeriod first second)
    (hSecondThird :
      DirectTransitionCompatible period hPeriod second third) :
    DirectTransitionCompatible period hPeriod first third := by
  let A₁₂ := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      first.chartAnchor second.chartAnchor)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current)
  let A₂₃ := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      second.chartAnchor third.chartAnchor)
    (extChartAt throatCoverModelWithCorners second.chartAnchor current)
  let A₁₃ := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      first.chartAnchor third.chartAnchor)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current)
  let B₁₂ (u v : ThroatCoverCoordinates) := fderiv Real
    (fderiv Real (throatGaugeBaseChartTransition period hPeriod
      first.chartAnchor second.chartAnchor))
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u v
  let B₂₃ (u v : ThroatCoverCoordinates) := fderiv Real
    (fderiv Real (throatGaugeBaseChartTransition period hPeriod
      second.chartAnchor third.chartAnchor))
    (extChartAt throatCoverModelWithCorners second.chartAnchor current) u v
  let B₁₃ (u v : ThroatCoverCoordinates) := fderiv Real
    (fderiv Real (throatGaugeBaseChartTransition period hPeriod
      first.chartAnchor third.chartAnchor))
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u v
  let D₁₂ : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      first.frameAnchor second.frameAnchor current
  let D₂₃ : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      second.frameAnchor third.frameAnchor current
  let D₁₃ : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      first.frameAnchor third.frameAnchor current
  let E₁₂ (u : ThroatCoverCoordinates) := fderiv Real
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
      first.frameAnchor second.frameAnchor first.chartAnchor)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u
  let E₂₃ (u : ThroatCoverCoordinates) := fderiv Real
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
      second.frameAnchor third.frameAnchor second.chartAnchor)
    (extChartAt throatCoverModelWithCorners second.chartAnchor current) u
  let E₁₃ (u : ThroatCoverCoordinates) := fderiv Real
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
      first.frameAnchor third.frameAnchor first.chartAnchor)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u
  let F₁₂ (u v : ThroatCoverCoordinates) := fderiv Real
    (fun coordinate => fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        first.frameAnchor second.frameAnchor first.chartAnchor) coordinate v)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u
  let F₂₃ (u v : ThroatCoverCoordinates) := fderiv Real
    (fun coordinate => fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        second.frameAnchor third.frameAnchor second.chartAnchor) coordinate v)
    (extChartAt throatCoverModelWithCorners second.chartAnchor current) u
  let F₁₃ (u v : ThroatCoverCoordinates) := fderiv Real
    (fun coordinate => fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        first.frameAnchor third.frameAnchor first.chartAnchor) coordinate v)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u
  have hFrames : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) first.frameAnchor).baseSet ∩
        ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) second.frameAnchor).baseSet ∩
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) third.frameAnchor).baseSet) :=
    ⟨first.frame_mem, second.frame_mem, third.frame_mem⟩
  have hA : A₁₃ = A₂₃.comp A₁₂ := by
    simpa only [A₁₂, A₂₃, A₁₃,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
        period hPeriod first.chartAnchor second.chartAnchor third.chartAnchor
          current first.chart_mem second.chart_mem third.chart_mem
  have hB : ∀ u v,
      B₁₃ u v = B₂₃ (A₁₂ u) (A₁₂ v) + A₂₃ (B₁₂ u v) := by
    intro u v
    simpa only [A₁₂, A₂₃, B₁₂, B₂₃, B₁₃,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
        period hPeriod first.chartAnchor second.chartAnchor third.chartAnchor
          current first.chart_mem second.chart_mem third.chart_mem u v
  have hD : D₁₃ = D₂₃.comp D₁₂ := by
    apply ContinuousLinearMap.ext
    intro covector
    have hCocycle := congrArg
      (fun transition : FramedCovector ThroatCoverCoordinates ≃L[Real]
          FramedCovector ThroatCoverCoordinates => transition covector)
      (throatGaugeCovectorTrivializationTransitionAt_cocycle period hPeriod
        first.frameAnchor second.frameAnchor third.frameAnchor current hFrames)
    simpa only [D₁₂, D₂₃, D₁₃,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.coe_coe] using hCocycle.symm
  have hE : ∀ u,
      E₁₃ u = D₂₃.comp (E₁₂ u) + (E₂₃ (A₁₂ u)).comp D₁₂ := by
    intro u
    simpa only [A₁₂, D₁₂, D₂₃, E₁₂, E₂₃, E₁₃,
      throatGaugeCovectorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners first.chartAnchor).left_inv
        first.chart_mem,
      (extChartAt throatCoverModelWithCorners second.chartAnchor).left_inv
        second.chart_mem] using
      throatGaugeFrameBaseChartTransition_firstDerivative_cocycle period hPeriod
        first.frameAnchor second.frameAnchor third.frameAnchor first.chartAnchor
          second.chartAnchor current hFrames first.chart_mem second.chart_mem u
  have hBase₁₂Derivative : DifferentiableAt Real
      (fderiv Real (throatGaugeBaseChartTransition period hPeriod
        first.chartAnchor second.chartAnchor))
      (extChartAt throatCoverModelWithCorners first.chartAnchor current) :=
    ((throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      first.chartAnchor second.chartAnchor current first.chart_mem
        second.chart_mem).fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)
  have hB₁₂Bridge (u v : ThroatCoverCoordinates) :
      fderiv Real
          (fun coordinate => fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              first.chartAnchor second.chartAnchor) coordinate v)
          (extChartAt throatCoverModelWithCorners first.chartAnchor current) u =
        B₁₂ u v := by
    simpa only [B₁₂] using
      fderiv_clm_apply_const_apply
        (fderiv Real (throatGaugeBaseChartTransition period hPeriod
          first.chartAnchor second.chartAnchor))
        (extChartAt throatCoverModelWithCorners first.chartAnchor current)
          u v hBase₁₂Derivative
  have hF : ∀ u v, F₁₃ u v =
      D₂₃.comp (F₁₂ u v) +
      (E₂₃ (A₁₂ u)).comp (E₁₂ v) +
      (E₂₃ (A₁₂ v)).comp (E₁₂ u) +
      (F₂₃ (A₁₂ u) (A₁₂ v)).comp D₁₂ +
      (E₂₃ (B₁₂ u v)).comp D₁₂ := by
    intro u v
    apply ContinuousLinearMap.ext
    intro covector
    simpa only [A₁₂, B₁₂, D₁₂, D₂₃, E₁₂, E₂₃, F₁₂, F₂₃, F₁₃,
      throatGaugeCovectorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners first.chartAnchor).left_inv
        first.chart_mem,
      (extChartAt throatCoverModelWithCorners second.chartAnchor).left_inv
        second.chart_mem,
      ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearEquiv.coe_coe, hB₁₂Bridge u v] using
      throatGaugeFrameBaseChartTransition_secondDerivative_cocycle_apply
        period hPeriod first.frameAnchor second.frameAnchor third.frameAnchor
          first.chartAnchor second.chartAnchor current hFrames first.chart_mem
            second.chart_mem u v covector
  have hFirst₁₂ : ∀ u,
      second.jet.firstDerivative (A₁₂ u) =
        D₁₂ (first.jet.firstDerivative u) + E₁₂ u first.jet.value := by
    intro u
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates => derivative u)
      hFirstSecond.firstDerivative_transition
    simpa only [A₁₂, D₁₂, E₁₂,
      ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.flip_apply] using hApplied
  have hFirst₂₃ : ∀ u,
      third.jet.firstDerivative (A₂₃ u) =
        D₂₃ (second.jet.firstDerivative u) + E₂₃ u second.jet.value := by
    intro u
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates => derivative u)
      hSecondThird.firstDerivative_transition
    simpa only [A₂₃, D₂₃, E₂₃,
      ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.flip_apply] using hApplied
  have hSecond₁₂ : ∀ u v,
      second.jet.secondDerivative (A₁₂ u) (A₁₂ v) +
          second.jet.firstDerivative (B₁₂ u v) =
        D₁₂ (first.jet.secondDerivative u v) +
          E₁₂ u (first.jet.firstDerivative v) +
          E₁₂ v (first.jet.firstDerivative u) + F₁₂ u v first.jet.value := by
    intro u v
    simpa only [A₁₂, B₁₂, D₁₂, E₁₂, F₁₂,
      ContinuousLinearEquiv.coe_coe] using
      hFirstSecond.secondDerivative_transition u v
  have hSecond₂₃ : ∀ u v,
      third.jet.secondDerivative (A₂₃ u) (A₂₃ v) +
          third.jet.firstDerivative (B₂₃ u v) =
        D₂₃ (second.jet.secondDerivative u v) +
          E₂₃ u (second.jet.firstDerivative v) +
          E₂₃ v (second.jet.firstDerivative u) + F₂₃ u v second.jet.value := by
    intro u v
    simpa only [A₂₃, B₂₃, D₂₃, E₂₃, F₂₃,
      ContinuousLinearEquiv.coe_coe] using
      hSecondThird.secondDerivative_transition u v
  constructor
  · rw [hSecondThird.value_transition, hFirstSecond.value_transition]
    exact (congrArg
      (fun transition : FramedCovector ThroatCoverCoordinates →L[Real]
        FramedCovector ThroatCoverCoordinates => transition first.jet.value)
      hD).symm
  · apply ContinuousLinearMap.ext
    intro u
    exact directFirstTransition_trans A₁₂ A₂₃ A₁₃ D₁₂ D₂₃ D₁₃ E₁₂ E₂₃ E₁₃
      first.jet.value second.jet.value first.jet.firstDerivative
        second.jet.firstDerivative third.jet.firstDerivative hA hD hE
          hFirstSecond.value_transition hFirst₁₂ hFirst₂₃ u
  · intro u v
    exact directSecondTransition_trans A₁₂ A₂₃ A₁₃ B₁₂ B₂₃ B₁₃
      D₁₂ D₂₃ D₁₃ E₁₂ E₂₃ E₁₃ F₁₂ F₂₃ F₁₃
      first.jet.value second.jet.value first.jet.firstDerivative
        second.jet.firstDerivative third.jet.firstDerivative
        first.jet.secondDerivative second.jet.secondDerivative
          third.jet.secondDerivative hA hB hD hE hF
            hFirstSecond.value_transition hFirst₁₂ hFirst₂₃ hSecond₁₂ hSecond₂₃ u v

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectTransitivity4D
end JanusFormal

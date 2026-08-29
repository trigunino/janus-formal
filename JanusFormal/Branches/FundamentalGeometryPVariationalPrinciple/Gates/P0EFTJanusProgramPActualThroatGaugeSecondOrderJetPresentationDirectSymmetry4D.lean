import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

/-!
# Symmetry of direct throat gauge second-jet compatibility

The inverse base-chart and varying-frame laws invert the exact value,
Jacobian and Hessian transition laws of arbitrary local presentations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSymmetry4D

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
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderGroupoid4D
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

private theorem directFirstTransition_symm
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    (A Ainv : X →L[Real] X)
    (D Dinv : V →L[Real] V)
    (E Einv : X → V →L[Real] V)
    (p₀ q₀ : V) (p₁ q₁ : X →L[Real] V)
    (hA : A.comp Ainv = ContinuousLinearMap.id Real X)
    (hD : Dinv.comp D = ContinuousLinearMap.id Real V)
    (hE : ∀ u, Dinv.comp (E u) + (Einv (A u)).comp D = 0)
    (h₀ : q₀ = D p₀)
    (h₁ : ∀ u, q₁ (A u) = D (p₁ u) + E u p₀)
    (w : X) :
    p₁ (Ainv w) = Dinv (q₁ w) + Einv w q₀ := by
  have hw : A (Ainv w) = w := by
    have hApplied := congrArg (fun map : X →L[Real] X => map w) hA
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hDApply (value : V) : Dinv (D value) = value := by
    have hApplied := congrArg (fun map : V →L[Real] V => map value) hD
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hEApply (u : X) (value : V) :
      Dinv (E u value) + Einv (A u) (D value) = 0 := by
    have hApplied := congrArg
      (fun map : V →L[Real] V => map value) (hE u)
    simpa only [add_apply,
      ContinuousLinearMap.comp_apply, zero_apply] using hApplied
  have hForward := h₁ (Ainv w)
  rw [hw] at hForward
  have hFrameCancel := hEApply (Ainv w) p₀
  rw [hw] at hFrameCancel
  rw [hForward, h₀, map_add, hDApply]
  calc
    p₁ (Ainv w) = p₁ (Ainv w) + 0 := by simp
    _ = p₁ (Ainv w) +
        (Dinv (E (Ainv w) p₀) + Einv w (D p₀)) := by
          rw [hFrameCancel]
    _ = p₁ (Ainv w) + Dinv (E (Ainv w) p₀) +
        Einv w (D p₀) := by abel

private theorem directSecondTransition_symm
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    (A Ainv : X →L[Real] X)
    (B Binv : X → X → X)
    (D Dinv : V →L[Real] V)
    (E Einv : X → V →L[Real] V)
    (F Finv : X → X → V →L[Real] V)
    (p₀ q₀ : V)
    (p₁ q₁ : X →L[Real] V)
    (p₂ q₂ : X →L[Real] X →L[Real] V)
    (hA : A.comp Ainv = ContinuousLinearMap.id Real X)
    (hB : ∀ u v, Binv (A u) (A v) + Ainv (B u v) = 0)
    (hD : Dinv.comp D = ContinuousLinearMap.id Real V)
    (hE : ∀ u, Dinv.comp (E u) + (Einv (A u)).comp D = 0)
    (hF : ∀ u v value,
      Dinv (F u v value) +
      Einv (A u) (E v value) +
      Einv (A v) (E u value) +
      Finv (A u) (A v) (D value) +
      Einv (B u v) (D value) = 0)
    (h₀ : q₀ = D p₀)
    (h₁ : ∀ u, q₁ (A u) = D (p₁ u) + E u p₀)
    (h₁Symm : ∀ w, p₁ (Ainv w) = Dinv (q₁ w) + Einv w q₀)
    (h₂ : ∀ u v,
      q₂ (A u) (A v) + q₁ (B u v) =
        D (p₂ u v) + E u (p₁ v) + E v (p₁ u) + F u v p₀)
    (w z : X) :
    p₂ (Ainv w) (Ainv z) + p₁ (Binv w z) =
      Dinv (q₂ w z) + Einv w (q₁ z) + Einv z (q₁ w) +
        Finv w z q₀ := by
  let u := Ainv w
  let v := Ainv z
  have hw : A u = w := by
    have hApplied := congrArg (fun map : X →L[Real] X => map w) hA
    simpa only [u, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hz : A v = z := by
    have hApplied := congrArg (fun map : X →L[Real] X => map z) hA
    simpa only [v, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hDApply (value : V) : Dinv (D value) = value := by
    have hApplied := congrArg (fun map : V →L[Real] V => map value) hD
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hEApply (direction : X) (value : V) :
      Einv (A direction) (D value) = -Dinv (E direction value) := by
    apply eq_neg_of_add_eq_zero_right
    have hApplied := congrArg
      (fun map : V →L[Real] V => map value) (hE direction)
    simpa only [add_apply,
      ContinuousLinearMap.comp_apply, zero_apply] using hApplied
  have hBase : Binv (A u) (A v) = -Ainv (B u v) :=
    eq_neg_of_add_eq_zero_left (hB u v)
  have hSecondApplied := congrArg Dinv (h₂ u v)
  simp only [map_add] at hSecondApplied
  rw [hDApply] at hSecondApplied
  have hQ₂ :
      Dinv (q₂ (A u) (A v)) =
        p₂ u v + Dinv (E u (p₁ v)) + Dinv (E v (p₁ u)) +
          Dinv (F u v p₀) - Dinv (q₁ (B u v)) := by
    calc
      Dinv (q₂ (A u) (A v)) =
          (Dinv (q₂ (A u) (A v)) + Dinv (q₁ (B u v))) -
            Dinv (q₁ (B u v)) := by abel
      _ = p₂ u v + Dinv (E u (p₁ v)) + Dinv (E v (p₁ u)) +
          Dinv (F u v p₀) - Dinv (q₁ (B u v)) := by
            rw [hSecondApplied]
  have hFWithoutLast :
      Dinv (F u v p₀) +
          Einv (A u) (E v p₀) + Einv (A v) (E u p₀) +
          Finv (A u) (A v) (D p₀) = -Einv (B u v) (D p₀) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [] using hF u v p₀
  have hNormalized :
      p₂ u v + p₁ (Binv (A u) (A v)) =
        Dinv (q₂ (A u) (A v)) + Einv (A u) (q₁ (A v)) +
          Einv (A v) (q₁ (A u)) + Finv (A u) (A v) q₀ := by
    rw [hBase, map_neg, h₁Symm, h₀, h₁, h₁, hQ₂]
    simp only [map_add]
    rw [hEApply u, hEApply v]
    have hCancellation :
        Dinv (E u (p₁ v)) + Dinv (E v (p₁ u)) + Dinv (F u v p₀) +
            (-Dinv (E u (p₁ v)) + Einv (A u) (E v p₀)) +
            (-Dinv (E v (p₁ u)) + Einv (A v) (E u p₀)) +
            Finv (A u) (A v) (D p₀) = -Einv (B u v) (D p₀) := by
      calc
        Dinv (E u (p₁ v)) + Dinv (E v (p₁ u)) + Dinv (F u v p₀) +
              (-Dinv (E u (p₁ v)) + Einv (A u) (E v p₀)) +
              (-Dinv (E v (p₁ u)) + Einv (A v) (E u p₀)) +
              Finv (A u) (A v) (D p₀) =
            Dinv (F u v p₀) + Einv (A u) (E v p₀) +
              Einv (A v) (E u p₀) + Finv (A u) (A v) (D p₀) := by abel
        _ = -Einv (B u v) (D p₀) := hFWithoutLast
    calc
      p₂ u v + (-(Dinv (q₁ (B u v)) + Einv (B u v) (D p₀))) =
          p₂ u v - Dinv (q₁ (B u v)) - Einv (B u v) (D p₀) := by abel
      _ = p₂ u v - Dinv (q₁ (B u v)) +
          (Dinv (E u (p₁ v)) + Dinv (E v (p₁ u)) + Dinv (F u v p₀) +
            (-Dinv (E u (p₁ v)) + Einv (A u) (E v p₀)) +
            (-Dinv (E v (p₁ u)) + Einv (A v) (E u p₀)) +
            Finv (A u) (A v) (D p₀)) := by rw [hCancellation]; abel
      _ = p₂ u v + Dinv (E u (p₁ v)) + Dinv (E v (p₁ u)) +
            Dinv (F u v p₀) - Dinv (q₁ (B u v)) +
            (-Dinv (E u (p₁ v)) + Einv (A u) (E v p₀)) +
            (-Dinv (E v (p₁ u)) + Einv (A v) (E u p₀)) +
            Finv (A u) (A v) (D p₀) := by abel
  simpa only [u, v, hw, hz] using hNormalized

/-! ## Exact symmetry -/

/-- Direct compatibility is symmetric already, before taking its generated
equivalence closure. -/
theorem directTransitionCompatible_symm
    {current : EffectiveThroat period hPeriod}
    {first second :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current}
    (hDirect : DirectTransitionCompatible period hPeriod first second) :
    DirectTransitionCompatible period hPeriod second first := by
  let A₁₂ := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      first.chartAnchor second.chartAnchor)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current)
  let A₂₁ := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      second.chartAnchor first.chartAnchor)
    (extChartAt throatCoverModelWithCorners second.chartAnchor current)
  let B₁₂ (u v : ThroatCoverCoordinates) := fderiv Real
    (fderiv Real (throatGaugeBaseChartTransition period hPeriod
      first.chartAnchor second.chartAnchor))
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u v
  let B₂₁ (u v : ThroatCoverCoordinates) := fderiv Real
    (fderiv Real (throatGaugeBaseChartTransition period hPeriod
      second.chartAnchor first.chartAnchor))
    (extChartAt throatCoverModelWithCorners second.chartAnchor current) u v
  let D₁₂ : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      first.frameAnchor second.frameAnchor current
  let D₂₁ : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      second.frameAnchor first.frameAnchor current
  let E₁₂ (u : ThroatCoverCoordinates) := fderiv Real
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
      first.frameAnchor second.frameAnchor first.chartAnchor)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u
  let E₂₁ (u : ThroatCoverCoordinates) := fderiv Real
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
      second.frameAnchor first.frameAnchor second.chartAnchor)
    (extChartAt throatCoverModelWithCorners second.chartAnchor current) u
  let F₁₂ (u v : ThroatCoverCoordinates) := fderiv Real
    (fun coordinate => fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        first.frameAnchor second.frameAnchor first.chartAnchor) coordinate v)
    (extChartAt throatCoverModelWithCorners first.chartAnchor current) u
  let F₂₁ (u v : ThroatCoverCoordinates) := fderiv Real
    (fun coordinate => fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        second.frameAnchor first.frameAnchor second.chartAnchor) coordinate v)
    (extChartAt throatCoverModelWithCorners second.chartAnchor current) u
  have hA : A₁₂.comp A₂₁ =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [A₁₂, A₂₁,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_inverse
        period hPeriod second.chartAnchor first.chartAnchor current
          second.chart_mem first.chart_mem
  have hB : ∀ u v, B₂₁ (A₁₂ u) (A₁₂ v) + A₂₁ (B₁₂ u v) = 0 := by
    intro u v
    simpa only [A₁₂, A₂₁, B₁₂, B₂₁,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_inverse_apply
        period hPeriod first.chartAnchor second.chartAnchor current
          first.chart_mem second.chart_mem u v
  have hD : D₂₁.comp D₁₂ = ContinuousLinearMap.id Real
      (FramedCovector ThroatCoverCoordinates) := by
    apply ContinuousLinearMap.ext
    intro covector
    have hCocycle := congrArg
      (fun transition : FramedCovector ThroatCoverCoordinates ≃L[Real]
          FramedCovector ThroatCoverCoordinates => transition covector)
      (throatGaugeCovectorTrivializationTransitionAt_cocycle period hPeriod
        first.frameAnchor second.frameAnchor first.frameAnchor current
          ⟨first.frame_mem, second.frame_mem, first.frame_mem⟩)
    have hSelf :
        throatGaugeCovectorTrivializationTransitionAt period hPeriod
            first.frameAnchor first.frameAnchor current covector = covector := by
      simpa only [throatGaugeCovectorTransitionCenteredChart,
        (extChartAt throatCoverModelWithCorners first.chartAnchor).left_inv
          first.chart_mem, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearMap.id_apply] using congrArg
        (fun transition : FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates => transition covector)
        (throatGaugeCovectorTransitionCenteredChart_self period hPeriod
          first.frameAnchor first.chartAnchor current first.frame_mem first.chart_mem)
    simpa only [D₁₂, D₂₁, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, hSelf] using hCocycle
  have hE : ∀ u, D₂₁.comp (E₁₂ u) + (E₂₁ (A₁₂ u)).comp D₁₂ = 0 := by
    intro u
    simpa only [A₁₂, D₁₂, D₂₁, E₁₂, E₂₁,
      throatGaugeCovectorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners first.chartAnchor).left_inv
        first.chart_mem,
      (extChartAt throatCoverModelWithCorners second.chartAnchor).left_inv
        second.chart_mem] using
      throatGaugeFrameBaseChartTransition_firstDerivative_inverse period hPeriod
        first.frameAnchor second.frameAnchor first.chartAnchor second.chartAnchor
          current ⟨first.frame_mem, second.frame_mem⟩ first.chart_mem second.chart_mem u
  have hBaseDerivative : DifferentiableAt Real
      (fderiv Real (throatGaugeBaseChartTransition period hPeriod
        first.chartAnchor second.chartAnchor))
      (extChartAt throatCoverModelWithCorners first.chartAnchor current) :=
    ((throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      first.chartAnchor second.chartAnchor current first.chart_mem
        second.chart_mem).fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)
  have hBBridge (u v : ThroatCoverCoordinates) :
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
          u v hBaseDerivative
  have hF : ∀ u v value,
      D₂₁ (F₁₂ u v value) + E₂₁ (A₁₂ u) (E₁₂ v value) +
      E₂₁ (A₁₂ v) (E₁₂ u value) +
      F₂₁ (A₁₂ u) (A₁₂ v) (D₁₂ value) +
      E₂₁ (B₁₂ u v) (D₁₂ value) = 0 := by
    intro u v value
    simpa only [A₁₂, B₁₂, D₁₂, D₂₁, E₁₂, E₂₁, F₁₂, F₂₁,
      throatGaugeCovectorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners first.chartAnchor).left_inv
        first.chart_mem,
      (extChartAt throatCoverModelWithCorners second.chartAnchor).left_inv
        second.chart_mem, ContinuousLinearEquiv.coe_coe,
      hBBridge u v] using
      throatGaugeFrameBaseChartTransition_secondDerivative_inverse_apply
        period hPeriod first.frameAnchor second.frameAnchor first.chartAnchor
          second.chartAnchor current ⟨first.frame_mem, second.frame_mem⟩
            first.chart_mem second.chart_mem u v value
  have hFirst : ∀ u,
      second.jet.firstDerivative (A₁₂ u) =
        D₁₂ (first.jet.firstDerivative u) + E₁₂ u first.jet.value := by
    intro u
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates => derivative u)
      hDirect.firstDerivative_transition
    simpa only [A₁₂, D₁₂, E₁₂,
      ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.flip_apply] using hApplied
  have hFirstSymm : ∀ w,
      first.jet.firstDerivative (A₂₁ w) =
        D₂₁ (second.jet.firstDerivative w) + E₂₁ w second.jet.value :=
    directFirstTransition_symm A₁₂ A₂₁ D₁₂ D₂₁ E₁₂ E₂₁
      first.jet.value second.jet.value first.jet.firstDerivative
        second.jet.firstDerivative hA hD hE hDirect.value_transition hFirst
  have hSecond : ∀ u v,
      second.jet.secondDerivative (A₁₂ u) (A₁₂ v) +
          second.jet.firstDerivative (B₁₂ u v) =
        D₁₂ (first.jet.secondDerivative u v) +
          E₁₂ u (first.jet.firstDerivative v) +
          E₁₂ v (first.jet.firstDerivative u) + F₁₂ u v first.jet.value := by
    intro u v
    simpa only [A₁₂, B₁₂, D₁₂, E₁₂, F₁₂,
      ContinuousLinearEquiv.coe_coe] using
      hDirect.secondDerivative_transition u v
  constructor
  · rw [hDirect.value_transition]
    have hApplied := congrArg
      (fun map : FramedCovector ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates => map first.jet.value) hD
    simpa only [D₁₂, D₂₁, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe] using hApplied.symm
  · apply ContinuousLinearMap.ext
    intro w
    exact hFirstSymm w
  · intro w z
    exact directSecondTransition_symm A₁₂ A₂₁ B₁₂ B₂₁
      D₁₂ D₂₁ E₁₂ E₂₁ F₁₂ F₂₁
      first.jet.value second.jet.value first.jet.firstDerivative
        second.jet.firstDerivative first.jet.secondDerivative
          second.jet.secondDerivative hA hB hD hE hF hDirect.value_transition
            hFirst hFirstSymm hSecond w z

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSymmetry4D
end JanusFormal

import Mathlib

namespace JanusFormal
namespace P0EFTJanusReducedTwoMetricEulerNoether

set_option autoImplicit false

noncomputable section

variable {Configuration : Type*}
variable [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]

/-- A reduced chart selecting one amplitude and one independent variation in
each metric sector.  This is finite-dimensional candidate data, not the full
Janus metric field space or a derivation of a published cross density. -/
structure TwoMetricReducedChart (Configuration : Type*)
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration] where
  plusCoordinate : Configuration →L[ℝ] ℝ
  minusCoordinate : Configuration →L[ℝ] ℝ
  plusVariation : Configuration
  minusVariation : Configuration
  plusCoordinate_plus : plusCoordinate plusVariation = 1
  plusCoordinate_minus : plusCoordinate minusVariation = 0
  minusCoordinate_plus : minusCoordinate plusVariation = 0
  minusCoordinate_minus : minusCoordinate minusVariation = 1

/-- Relative metric mode in the supplied reduced chart. -/
def relativeMode (chart : TwoMetricReducedChart Configuration) :
    Configuration →L[ℝ] ℝ :=
  chart.plusCoordinate - chart.minusCoordinate

/-- Explicit quadratic action for the relative reduced metric mode. -/
def reducedInteractionAction
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) : ℝ :=
  coupling / 2 * (relativeMode chart q) ^ 2

/-- Euler coefficient extracted by the independent plus variation. -/
def plusEuler
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) : ℝ :=
  coupling * relativeMode chart q

/-- Euler coefficient extracted by the independent minus variation. -/
def minusEuler
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) : ℝ :=
  -coupling * relativeMode chart q

/-- Displayed first-variation functional of the reduced action. -/
def reducedEuler
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) : Configuration →L[ℝ] ℝ :=
  (coupling * relativeMode chart q) • relativeMode chart

/-- The displayed Euler functional is the genuine Fréchet derivative of the
explicit reduced action. -/
theorem reducedInteractionAction_hasFDerivAt
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    HasFDerivAt (reducedInteractionAction chart coupling)
      (reducedEuler chart coupling q) q := by
  have hAction :
      HasFDerivAt
        (fun x : Configuration ↦ coupling / 2 * (relativeMode chart x) ^ 2)
        ((coupling / 2) •
          (((2 : ℕ) • (relativeMode chart q) ^ (2 - 1)) •
            relativeMode chart)) q :=
    ((relativeMode chart).hasFDerivAt.pow 2).const_mul (coupling / 2)
  have hDisplayed :
      (coupling / 2) •
          (((2 : ℕ) • (relativeMode chart q) ^ (2 - 1)) •
            relativeMode chart) =
        reducedEuler chart coupling q := by
    apply ContinuousLinearMap.ext
    intro variation
    simp [reducedEuler]
    ring
  rw [← hDisplayed]
  change HasFDerivAt
    (fun x : Configuration ↦ coupling / 2 * (relativeMode chart x) ^ 2)
    ((coupling / 2) •
      (((2 : ℕ) • (relativeMode chart q) ^ (2 - 1)) •
        relativeMode chart)) q
  exact hAction

/-- An actual independent plus variation reads off the plus Euler
coefficient. -/
theorem fderiv_plus_variation
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    fderiv ℝ (reducedInteractionAction chart coupling) q
        chart.plusVariation =
      plusEuler chart coupling q := by
  rw [(reducedInteractionAction_hasFDerivAt chart coupling q).fderiv]
  simp [reducedEuler, relativeMode, plusEuler,
    chart.plusCoordinate_plus, chart.minusCoordinate_plus]

/-- An actual independent minus variation reads off the minus Euler
coefficient. -/
theorem fderiv_minus_variation
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    fderiv ℝ (reducedInteractionAction chart coupling) q
        chart.minusVariation =
      minusEuler chart coupling q := by
  rw [(reducedInteractionAction_hasFDerivAt chart coupling q).fderiv]
  simp [reducedEuler, relativeMode, minusEuler,
    chart.plusCoordinate_minus, chart.minusCoordinate_minus]

/-- Independent stationarity is exactly the pair of Euler equations. -/
theorem independent_variations_iff_both_euler_zero
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    (fderiv ℝ (reducedInteractionAction chart coupling) q
          chart.plusVariation = 0 ∧
        fderiv ℝ (reducedInteractionAction chart coupling) q
          chart.minusVariation = 0) ↔
      plusEuler chart coupling q = 0 ∧
        minusEuler chart coupling q = 0 := by
  rw [fderiv_plus_variation, fderiv_minus_variation]

/-- Full stationarity of this two-coordinate action is also equivalent to the
two independently extracted Euler equations. -/
theorem full_stationarity_iff_both_euler_zero
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    fderiv ℝ (reducedInteractionAction chart coupling) q = 0 ↔
      plusEuler chart coupling q = 0 ∧
        minusEuler chart coupling q = 0 := by
  rw [(reducedInteractionAction_hasFDerivAt chart coupling q).fderiv]
  constructor
  · intro hZero
    have hPlus := congrArg
      (fun euler : Configuration →L[ℝ] ℝ ↦ euler chart.plusVariation)
      hZero
    have hMinus := congrArg
      (fun euler : Configuration →L[ℝ] ℝ ↦ euler chart.minusVariation)
      hZero
    constructor
    · simpa [reducedEuler, relativeMode, plusEuler,
        chart.plusCoordinate_plus, chart.minusCoordinate_plus] using hPlus
    · simpa [reducedEuler, relativeMode, minusEuler,
        chart.plusCoordinate_minus, chart.minusCoordinate_minus] using hMinus
  · rintro ⟨hPlus, _⟩
    have hCoefficient : coupling * relativeMode chart q = 0 := by
      simpa only [plusEuler] using hPlus
    apply ContinuousLinearMap.ext
    intro variation
    simp [reducedEuler, hCoefficient]

/-- The diagonal linked variation `(h,h)` relevant to the common Noether
symmetry.  It is distinct from the sign-linked `(h,-h)` convention. -/
def diagonalVariation
    (chart : TwoMetricReducedChart Configuration) : Configuration :=
  chart.plusVariation + chart.minusVariation

/-- The sign-linked variation, recorded separately to avoid conflating it with
the diagonal Noether direction. -/
def signLinkedVariation
    (chart : TwoMetricReducedChart Configuration) : Configuration :=
  chart.plusVariation - chart.minusVariation

/-- A diagonal linked variation sees only the sum of the two Euler
coefficients. -/
theorem diagonal_variation_sees_only_euler_sum
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    fderiv ℝ (reducedInteractionAction chart coupling) q
        (diagonalVariation chart) =
      plusEuler chart coupling q + minusEuler chart coupling q := by
  rw [(reducedInteractionAction_hasFDerivAt chart coupling q).fderiv]
  simp [diagonalVariation, reducedEuler, relativeMode, plusEuler, minusEuler,
    chart.plusCoordinate_plus, chart.plusCoordinate_minus,
    chart.minusCoordinate_plus, chart.minusCoordinate_minus]

/-- The distinct sign-linked variation sees the difference of the two Euler
coefficients. -/
theorem sign_linked_variation_sees_euler_difference
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    fderiv ℝ (reducedInteractionAction chart coupling) q
        (signLinkedVariation chart) =
      plusEuler chart coupling q - minusEuler chart coupling q := by
  rw [(reducedInteractionAction_hasFDerivAt chart coupling q).fderiv]
  simp [signLinkedVariation, reducedEuler, relativeMode, plusEuler, minusEuler,
    chart.plusCoordinate_plus, chart.plusCoordinate_minus,
    chart.minusCoordinate_plus, chart.minusCoordinate_minus]
  ring

/-- Translation along the common diagonal reduced variation. -/
def diagonalTranslate
    (chart : TwoMetricReducedChart Configuration)
    (parameter : ℝ) (q : Configuration) : Configuration :=
  q + parameter • diagonalVariation chart

/-- A supplied action symmetry under simultaneous reduced translations. -/
def DiagonalTranslationInvariant
    (chart : TwoMetricReducedChart Configuration)
    (action : Configuration → ℝ) : Prop :=
  ∀ q parameter, action (diagonalTranslate chart parameter q) = action q

theorem diagonalTranslate_hasDerivAt
    (chart : TwoMetricReducedChart Configuration)
    (q : Configuration) (parameter : ℝ) :
    HasDerivAt (fun t ↦ diagonalTranslate chart t q)
      (diagonalVariation chart) parameter := by
  simpa [diagonalTranslate] using
    ((hasDerivAt_id parameter).smul_const
      (diagonalVariation chart)).const_add q

/-- Reduced diagonal Noether theorem: a supplied finite symmetry forces the
actual Euler derivative to annihilate the common linked generator. -/
theorem diagonal_noether_of_translation_invariance
    (chart : TwoMetricReducedChart Configuration)
    (action : Configuration → ℝ)
    (euler : Configuration → Configuration →L[ℝ] ℝ)
    (hGradient : ∀ q, HasFDerivAt action (euler q) q)
    (hInvariant : DiagonalTranslationInvariant chart action)
    (q : Configuration) :
    euler q (diagonalVariation chart) = 0 := by
  let orbitAction : ℝ → ℝ := fun parameter ↦
    action (diagonalTranslate chart parameter q)
  have hOrbitDerivative :
      HasDerivAt orbitAction (euler q (diagonalVariation chart)) 0 := by
    have hComp :=
      (hGradient (diagonalTranslate chart 0 q)).comp_hasDerivAt 0
        (diagonalTranslate_hasDerivAt chart q 0)
    simpa [orbitAction, diagonalTranslate, Function.comp_def] using hComp
  have hOrbitConstant : orbitAction = fun _ ↦ action q := by
    funext parameter
    exact hInvariant q parameter
  have hZeroDerivative : HasDerivAt orbitAction 0 0 := by
    rw [hOrbitConstant]
    exact hasDerivAt_const (x := (0 : ℝ)) (c := action q)
  exact hOrbitDerivative.unique hZeroDerivative

/-- The explicit relative-mode action has the supplied diagonal symmetry. -/
theorem reducedInteractionAction_diagonal_invariant
    (chart : TwoMetricReducedChart Configuration) (coupling : ℝ) :
    DiagonalTranslationInvariant chart
      (reducedInteractionAction chart coupling) := by
  intro q parameter
  simp [reducedInteractionAction, diagonalTranslate, diagonalVariation,
    relativeMode, chart.plusCoordinate_plus, chart.plusCoordinate_minus,
    chart.minusCoordinate_plus, chart.minusCoordinate_minus]

/-- The combined Euler identity follows from the finite diagonal symmetry and
the actual derivative, rather than being postulated algebraically. -/
theorem reducedInteractionAction_diagonal_noether
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration) :
    plusEuler chart coupling q + minusEuler chart coupling q = 0 := by
  have hNoether := diagonal_noether_of_translation_invariance chart
    (reducedInteractionAction chart coupling) (reducedEuler chart coupling)
    (reducedInteractionAction_hasFDerivAt chart coupling)
    (reducedInteractionAction_diagonal_invariant chart coupling) q
  rw [← diagonal_variation_sees_only_euler_sum]
  simpa [(reducedInteractionAction_hasFDerivAt chart coupling q).fderiv]
    using hNoether

/-- Whenever the plus equation is nonzero, diagonal stationarity still holds
but cannot replace either independent Euler equation. -/
theorem diagonal_stationarity_strict_when_plus_euler_nonzero
    (chart : TwoMetricReducedChart Configuration)
    (coupling : ℝ) (q : Configuration)
    (hPlus : plusEuler chart coupling q ≠ 0) :
    fderiv ℝ (reducedInteractionAction chart coupling) q
          (diagonalVariation chart) = 0 ∧
      fderiv ℝ (reducedInteractionAction chart coupling) q
          chart.plusVariation ≠ 0 := by
  constructor
  · rw [diagonal_variation_sees_only_euler_sum,
      reducedInteractionAction_diagonal_noether]
  · rwa [fderiv_plus_variation]

end

end P0EFTJanusReducedTwoMetricEulerNoether
end JanusFormal

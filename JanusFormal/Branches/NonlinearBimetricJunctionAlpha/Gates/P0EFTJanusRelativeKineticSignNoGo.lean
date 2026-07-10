import Mathlib

namespace JanusFormal
namespace P0EFTJanusRelativeKineticSignNoGo

set_option autoImplicit false

/-- Two-mode reduction of the quadratic kinetic energy. -/
def kineticQuadraticForm
    (plusCoefficient minusCoefficient plusMode minusMode : ℝ) : ℝ :=
  plusCoefficient * plusMode ^ 2 + minusCoefficient * minusMode ^ 2

/-- Opposite Einstein-Hilbert kinetic signs give both positive and negative directions. -/
theorem opposite_sign_kinetic_form_is_indefinite
    (plusCoefficient minusCoefficient : ℝ)
    (hPlus : 0 < plusCoefficient)
    (hMinus : minusCoefficient < 0) :
    0 < kineticQuadraticForm plusCoefficient minusCoefficient 1 0 /\
      kineticQuadraticForm plusCoefficient minusCoefficient 0 1 < 0 := by
  constructor
  · simpa [kineticQuadraticForm] using hPlus
  · simpa [kineticQuadraticForm] using hMinus

/-- The negative direction scales quadratically. -/
theorem negative_mode_quadratic_scaling
    (plusCoefficient minusCoefficient amplitude : ℝ) :
    kineticQuadraticForm plusCoefficient minusCoefficient 0 amplitude =
      minusCoefficient * amplitude ^ 2 := by
  simp [kineticQuadraticForm]

/-- Arbitrarily large integer amplitudes preserve the negative direction. -/
theorem every_nonzero_negative_mode_has_negative_energy
    (plusCoefficient minusCoefficient amplitude : ℝ)
    (hMinus : minusCoefficient < 0)
    (hAmplitude : amplitude ≠ 0) :
    kineticQuadraticForm plusCoefficient minusCoefficient 0 amplitude < 0 := by
  rw [negative_mode_quadratic_scaling]
  exact mul_neg_of_neg_of_pos hMinus (sq_pos_of_ne_zero hAmplitude)

/--
A relative negative kinetic coefficient is therefore not a harmless sign
convention when both spin-2 modes propagate in an ordinary positive-definite
Hilbert space.  A consistent completion must prove at least one of the explicit
escape mechanisms below.
-/
structure RelativeKineticSignResolutionStatus where
  publishedRelativeNegativeSignTracked : Prop
  bothSpinTwoModesPropagate : Prop
  ordinaryPositiveHilbertSpaceUsed : Prop
  secondMetricIsAuxiliaryOrConstrained : Prop
  gaugeConstraintRemovesNegativeMode : Prop
  ptKreinQuantizationConstructed : Prop
  positiveSpectrumAndUnitarityProved : Prop
  bothEinsteinHilbertTermsRewrittenPositive : Prop
  negativeMassSignMovedToMatterOrCharge : Prop
  nonlinearHamiltonianBoundedBelow : Prop

/-- At least one non-ghost resolution must be active. -/
def relativeKineticSignResolved
    (s : RelativeKineticSignResolutionStatus) : Prop :=
  s.publishedRelativeNegativeSignTracked /\
  (s.secondMetricIsAuxiliaryOrConstrained \/
    s.gaugeConstraintRemovesNegativeMode \/
    (s.ptKreinQuantizationConstructed /\
      s.positiveSpectrumAndUnitarityProved) \/
    (s.bothEinsteinHilbertTermsRewrittenPositive /\
      s.negativeMassSignMovedToMatterOrCharge)) /\
  s.nonlinearHamiltonianBoundedBelow

/--
If both modes propagate in an ordinary positive Hilbert space, none of the
escape mechanisms is supplied, and the quadratic form has opposite signs, the
relative-sign problem remains open.
-/
structure UnresolvedRelativeSign where
  plusCoefficient : ℝ
  minusCoefficient : ℝ
  plusCoefficientPositive : 0 < plusCoefficient
  minusCoefficientNegative : minusCoefficient < 0
  bothModesPropagate : Prop
  ordinaryPositiveHilbertSpace : Prop
  noAuxiliaryReduction : Prop
  noGaugeRemoval : Prop
  noPTKreinCompletion : Prop
  noPositiveKineticRewrite : Prop

end P0EFTJanusRelativeKineticSignNoGo
end JanusFormal

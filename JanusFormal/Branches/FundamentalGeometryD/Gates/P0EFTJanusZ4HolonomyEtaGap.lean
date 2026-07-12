import Mathlib

namespace JanusFormal
namespace P0EFTJanusZ4HolonomyEtaGap

set_option autoImplicit false

/--
Algebraic value of the reduced eta invariant of the shifted circle operator for
holonomy parameter `a` in the fundamental interval: `eta(0)=1-2a`.

The formula is encoded algebraically here; deriving it from the Hurwitz-zeta
continuation remains an analytic theorem.
-/
def reducedCircleEtaModel (holonomy : ℚ) : ℚ :=
  1 - 2 * holonomy

@[simp] theorem quarter_holonomy_reduced_eta :
    reducedCircleEtaModel (1 / 4) = 1 / 2 := by
  norm_num [reducedCircleEtaModel]

/-- Chiral monopole zero modes multiply the one-dimensional reduced eta value. -/
def chiralReducedEtaModel
    (chernNumber : ℤ) (holonomy : ℚ) : ℚ :=
  (chernNumber : ℚ) * reducedCircleEtaModel holonomy

@[simp] theorem primitive_positive_quarter_eta :
    chiralReducedEtaModel 1 (1 / 4) = 1 / 2 := by
  norm_num [chiralReducedEtaModel, reducedCircleEtaModel]

@[simp] theorem primitive_negative_quarter_eta :
    chiralReducedEtaModel (-1) (1 / 4) = -1 / 2 := by
  norm_num [chiralReducedEtaModel, reducedCircleEtaModel]

/-- PT-related primitive monopole sectors cancel their reduced eta values. -/
theorem pt_paired_chiral_eta_cancels
    (chernNumber : ℤ) (holonomy : ℚ) :
    chiralReducedEtaModel chernNumber holonomy +
      chiralReducedEtaModel (-chernNumber) holonomy = 0 := by
  unfold chiralReducedEtaModel
  push_cast
  ring

/--
Geometric data for the lowest quarter-holonomy circle momentum on a product
throat. The cleared gap law is

`4 * gap^2 * L^2 * T^2 = pi^2`,

because the lowest shifted momentum is `pi/(2*L*T)`.
-/
structure QuarterHolonomyGapData where
  geometricLength : ℝ
  circleModulus : ℝ
  piConstant : ℝ
  gapSquared : ℝ
  geometricLengthPositive : 0 < geometricLength
  circleModulusPositive : 0 < circleModulus
  piConstantPositive : 0 < piConstant
  gapSquaredPositive : 0 < gapSquared
  quarterGapLaw :
    4 * gapSquared * geometricLength ^ 2 * circleModulus ^ 2 =
      piConstant ^ 2
  unweightedSpectralIsotropy :
    circleModulus ^ 2 = 2 * piConstant ^ 2

/-- Spectral isotropy turns the quarter-holonomy gap into `8*gap^2*L^2=1`. -/
theorem quarter_gap_under_spectral_isotropy
    (s : QuarterHolonomyGapData) :
    8 * s.gapSquared * s.geometricLength ^ 2 = 1 := by
  have hGap := s.quarterGapLaw
  rw [s.unweightedSpectralIsotropy] at hGap
  have hFactor :
      s.piConstant ^ 2 *
        (8 * s.gapSquared * s.geometricLength ^ 2 - 1) = 0 := by
    calc
      s.piConstant ^ 2 *
          (8 * s.gapSquared * s.geometricLength ^ 2 - 1) =
        4 * s.gapSquared * s.geometricLength ^ 2 *
            (2 * s.piConstant ^ 2) - s.piConstant ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hGap
  have hPiSquareNonzero : s.piConstant ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt s.piConstantPositive)
  have hDifference :
      8 * s.gapSquared * s.geometricLength ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hPiSquareNonzero
  linarith

/-- The lowest squared Dirac gap is exactly `1/(8 L^2)` in cleared form. -/
theorem quarter_gap_is_one_eighth_inverse_area
    (s : QuarterHolonomyGapData) :
    8 * s.gapSquared * s.geometricLength ^ 2 = 1 :=
  quarter_gap_under_spectral_isotropy s

/--
The eta algebra and gap relation are explicit, but a physical claim requires the
actual Pin lift to impose quarter holonomy and an APS/Hurwitz-zeta calculation
to identify the regularized eta invariant with the model above.
-/
structure Z4EtaAnalyticStatus where
  pinLiftedOrderFourHolonomyDerived : Prop
  holonomyParameterOneQuarterDerived : Prop
  chiralZeroModeTowerIdentified : Prop
  hurwitzEtaContinuationDerived : Prop
  reducedEtaFormulaProved : Prop
  pairedFoldEtaCancellationProved : Prop
  determinantPhaseComputed : Prop
  regulatorAndCountertermChoiceFixed : Prop


def z4EtaAnalyticClosed (s : Z4EtaAnalyticStatus) : Prop :=
  s.pinLiftedOrderFourHolonomyDerived /\
  s.holonomyParameterOneQuarterDerived /\
  s.chiralZeroModeTowerIdentified /\
  s.hurwitzEtaContinuationDerived /\
  s.reducedEtaFormulaProved /\
  s.pairedFoldEtaCancellationProved /\
  s.determinantPhaseComputed /\
  s.regulatorAndCountertermChoiceFixed

end P0EFTJanusZ4HolonomyEtaGap
end JanusFormal

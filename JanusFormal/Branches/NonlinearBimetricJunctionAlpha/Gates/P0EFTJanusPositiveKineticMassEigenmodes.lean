import Mathlib

namespace JanusFormal
namespace P0EFTJanusPositiveKineticMassEigenmodes

set_option autoImplicit false

/-- Unnormalized diagonal and relative spin-2 modes. -/
def diagonalMode (hPlus hMinus : ℝ) : ℝ := hPlus + hMinus

def relativeMode (hPlus hMinus : ℝ) : ℝ := hPlus - hMinus

/-- Exact orthogonal decomposition of the equal-coefficient kinetic form. -/
theorem kinetic_mode_decomposition (hPlus hMinus : ℝ) :
    2 * (hPlus ^ 2 + hMinus ^ 2) =
      diagonalMode hPlus hMinus ^ 2 +
        relativeMode hPlus hMinus ^ 2 := by
  unfold diagonalMode relativeMode
  ring

/-- Safe quadratic energy: positive kinetic term plus nonnegative relative mass. -/
def safeQuadraticEnergy
    (planckSquared relativeMassSquared hPlus hMinus : ℝ) : ℝ :=
  planckSquared * (hPlus ^ 2 + hMinus ^ 2) +
    relativeMassSquared * relativeMode hPlus hMinus ^ 2

/-- The diagonal mode is massless because the interaction depends only on the difference. -/
theorem equal_metric_fluctuations_have_zero_relative_mass
    (planckSquared relativeMassSquared h : ℝ) :
    safeQuadraticEnergy planckSquared relativeMassSquared h h =
      2 * planckSquared * h ^ 2 := by
  unfold safeQuadraticEnergy relativeMode
  ring

/-- A pure relative fluctuation carries the positive mass penalty. -/
theorem opposite_metric_fluctuations_energy
    (planckSquared relativeMassSquared h : ℝ) :
    safeQuadraticEnergy planckSquared relativeMassSquared h (-h) =
      2 * planckSquared * h ^ 2 +
        4 * relativeMassSquared * h ^ 2 := by
  unfold safeQuadraticEnergy relativeMode
  ring

/-- Positive kinetic coefficient and nonnegative relative mass give positive energy off zero. -/
theorem safe_quadratic_energy_positive
    (planckSquared relativeMassSquared hPlus hMinus : ℝ)
    (hPlanck : 0 < planckSquared)
    (hMass : 0 ≤ relativeMassSquared)
    (hMode : hPlus ≠ 0 ∨ hMinus ≠ 0) :
    0 < safeQuadraticEnergy
      planckSquared relativeMassSquared hPlus hMinus := by
  unfold safeQuadraticEnergy
  have hKineticPositive :
      0 < planckSquared * (hPlus ^ 2 + hMinus ^ 2) := by
    have hSumPositive : 0 < hPlus ^ 2 + hMinus ^ 2 := by
      rcases hMode with hPlusNonzero | hMinusNonzero
      · exact add_pos_of_pos_of_nonneg
          (sq_pos_of_ne_zero hPlusNonzero) (sq_nonneg hMinus)
      · exact add_pos_of_nonneg_of_pos
          (sq_nonneg hPlus) (sq_pos_of_ne_zero hMinusNonzero)
    exact mul_pos hPlanck hSumPositive
  have hMassNonnegative :
      0 ≤ relativeMassSquared * relativeMode hPlus hMinus ^ 2 :=
    mul_nonneg hMass (sq_nonneg _)
  exact add_pos_of_pos_of_nonneg hKineticPositive hMassNonnegative

/-- The interaction mass vanishes exactly on the diagonal subspace when its coefficient is positive. -/
theorem relative_mass_zero_iff_equal_metrics
    (relativeMassSquared hPlus hMinus : ℝ)
    (hMass : 0 < relativeMassSquared) :
    relativeMassSquared * relativeMode hPlus hMinus ^ 2 = 0 ↔
      hPlus = hMinus := by
  constructor
  · intro hZero
    have hCoefficient : relativeMassSquared ≠ 0 := ne_of_gt hMass
    have hSquare : relativeMode hPlus hMinus ^ 2 = 0 :=
      (mul_eq_zero.mp hZero).resolve_left hCoefficient
    have hRelative : relativeMode hPlus hMinus = 0 :=
      sq_eq_zero_iff.mp hSquare
    unfold relativeMode at hRelative
    linarith
  · intro hEqual
    rw [hEqual]
    simp [relativeMode]

/--
This reduced spectrum supplies the desired architecture: one massless diagonal
graviton and one positive-mass relative mode, without a negative kinetic
coefficient.
-/
structure LinearSpectrumClosureStatus where
  equalPositiveKineticCoefficientsDerived : Prop
  interactionDependsOnlyOnRelativeMode : Prop
  diagonalModeMassless : Prop
  relativeModeMassPositive : Prop
  physicalQuadraticEnergyPositive : Prop
  matterChargeSignsDerivedSeparately : Prop


def linearSpectrumClosed (s : LinearSpectrumClosureStatus) : Prop :=
  s.equalPositiveKineticCoefficientsDerived /\
  s.interactionDependsOnlyOnRelativeMode /\
  s.diagonalModeMassless /\
  s.relativeModeMassPositive /\
  s.physicalQuadraticEnergyPositive /\
  s.matterChargeSignsDerivedSeparately

end P0EFTJanusPositiveKineticMassEigenmodes
end JanusFormal

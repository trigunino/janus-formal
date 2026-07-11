import Mathlib

namespace JanusFormal
namespace P0EFTJanusWeightedSpectralLock

set_option autoImplicit false

/--
Cleared weighted balance between the first `S2` and `S1` modes.  The positive
weights may encode degeneracy, statistics and one-loop determinant factors.
-/
structure WeightedModeBalance where
  circleModulus : ℝ
  piConstant : ℝ
  sphereWeight : ℝ
  circleWeight : ℝ
  circleModulusPositive : 0 < circleModulus
  piConstantPositive : 0 < piConstant
  sphereWeightPositive : 0 < sphereWeight
  circleWeightPositive : 0 < circleWeight
  weightedBalance :
    sphereWeight * circleModulus ^ 2 =
      2 * circleWeight * piConstant ^ 2

/-- The unweighted case recovers `T^2 = 2*pi^2`. -/
theorem equal_weights_recover_unweighted_isotropy
    (s : WeightedModeBalance)
    (hWeights : s.sphereWeight = s.circleWeight) :
    s.circleModulus ^ 2 = 2 * s.piConstant ^ 2 := by
  rw [hWeights] at s.weightedBalance
  have hWeightNonzero : s.circleWeight ≠ 0 :=
    ne_of_gt s.circleWeightPositive
  have hFactor :
      s.circleWeight *
        (s.circleModulus ^ 2 - 2 * s.piConstant ^ 2) = 0 := by
    nlinarith [s.weightedBalance]
  have hDifference :=
    (mul_eq_zero.mp hFactor).resolve_left hWeightNonzero
  linarith

/-- Degeneracy weights `3` for `S2` and `2` for `S1` give `3*T^2=4*pi^2`. -/
theorem scalar_degeneracy_weights_fix_modified_modulus
    (s : WeightedModeBalance)
    (hSphere : s.sphereWeight = 3)
    (hCircle : s.circleWeight = 2) :
    3 * s.circleModulus ^ 2 = 4 * s.piConstant ^ 2 := by
  rw [hSphere, hCircle] at s.weightedBalance
  norm_num at s.weightedBalance ⊢
  linarith

/-- Positive weights determine at most one positive modulus. -/
theorem positive_weighted_modulus_unique
    (s₁ s₂ : WeightedModeBalance)
    (hPi : s₁.piConstant = s₂.piConstant)
    (hSphere : s₁.sphereWeight = s₂.sphereWeight)
    (hCircle : s₁.circleWeight = s₂.circleWeight) :
    s₁.circleModulus = s₂.circleModulus := by
  have h₁ := s₁.weightedBalance
  have h₂ := s₂.weightedBalance
  rw [← hPi, ← hSphere, ← hCircle] at h₂
  have hWeightNonzero : s₁.sphereWeight ≠ 0 :=
    ne_of_gt s₁.sphereWeightPositive
  have hFactor :
      s₁.sphereWeight *
        (s₁.circleModulus ^ 2 - s₂.circleModulus ^ 2) = 0 := by
    nlinarith [h₁, h₂]
  have hSquares :
      s₁.circleModulus ^ 2 = s₂.circleModulus ^ 2 := by
    have hDifference :=
      (mul_eq_zero.mp hFactor).resolve_left hWeightNonzero
    linarith
  have hRootFactor :
      (s₁.circleModulus - s₂.circleModulus) *
        (s₁.circleModulus + s₂.circleModulus) = 0 := by
    nlinarith [hSquares]
  rcases mul_eq_zero.mp hRootFactor with hDifference | hSum
  · linarith
  · have hPositive :
        0 < s₁.circleModulus + s₂.circleModulus :=
      add_pos s₁.circleModulusPositive s₂.circleModulusPositive
    exact False.elim ((ne_of_gt hPositive) hSum)

/-- Positive weighted mismatch energy. -/
def weightedMismatchEnergy
    (penalty sphereWeight circleWeight circleModulus piConstant : ℝ) : ℝ :=
  penalty *
    (sphereWeight * circleModulus ^ 2 -
      2 * circleWeight * piConstant ^ 2) ^ 2

/-- With positive penalty, zero energy is exactly the weighted balance law. -/
theorem weighted_mismatch_zero_iff_balance
    (penalty sphereWeight circleWeight circleModulus piConstant : ℝ)
    (hPenalty : 0 < penalty) :
    weightedMismatchEnergy penalty sphereWeight circleWeight
        circleModulus piConstant = 0 ↔
      sphereWeight * circleModulus ^ 2 =
        2 * circleWeight * piConstant ^ 2 := by
  constructor
  · intro hZero
    unfold weightedMismatchEnergy at hZero
    have hPenaltyNonzero : penalty ≠ 0 := ne_of_gt hPenalty
    have hSquare :
        (sphereWeight * circleModulus ^ 2 -
          2 * circleWeight * piConstant ^ 2) ^ 2 = 0 :=
      (mul_eq_zero.mp hZero).resolve_left hPenaltyNonzero
    nlinarith [hSquare]
  · intro hBalance
    unfold weightedMismatchEnergy
    rw [hBalance]
    ring

/--
The mode weights are therefore physical data.  Program D must derive them from
the actual field content and determinant, rather than assume equal weights.
-/
structure WeightedSpectralDerivationStatus where
  fieldContentDerivedFromGeometry : Prop
  sphereModeDegeneraciesComputed : Prop
  circleModeDegeneraciesComputed : Prop
  bosonFermionSignsComputed : Prop
  regularizedDeterminantWeightsComputed : Prop
  weightedVacuumLawDerived : Prop
  stableUniqueModulusDerived : Prop


def weightedSpectralDerivationClosed
    (s : WeightedSpectralDerivationStatus) : Prop :=
  s.fieldContentDerivedFromGeometry /\
  s.sphereModeDegeneraciesComputed /\
  s.circleModeDegeneraciesComputed /\
  s.bosonFermionSignsComputed /\
  s.regularizedDeterminantWeightsComputed /\
  s.weightedVacuumLawDerived /\
  s.stableUniqueModulusDerived

end P0EFTJanusWeightedSpectralLock
end JanusFormal

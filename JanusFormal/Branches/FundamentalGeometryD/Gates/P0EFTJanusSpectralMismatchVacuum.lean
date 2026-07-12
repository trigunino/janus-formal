import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpectralMismatchVacuum

set_option autoImplicit false

/--
Cleared first-mode mismatch on `S2_L x S1_(L*T)`.

After multiplying by positive powers of `L*T`, equality of the first sphere and
circle eigenvalues is equivalent to

`2*T^2 - 4*pi^2 = 0`.
-/
def clearedModeMismatch (circleModulus piConstant : ℝ) : ℝ :=
  2 * circleModulus ^ 2 - 4 * piConstant ^ 2

/-- Positive mismatch energy candidate. -/
def mismatchEnergy
    (weight circleModulus piConstant : ℝ) : ℝ :=
  weight * clearedModeMismatch circleModulus piConstant ^ 2

/-- Positive weight makes the mismatch energy nonnegative. -/
theorem mismatch_energy_nonnegative
    (weight circleModulus piConstant : ℝ)
    (hWeight : 0 ≤ weight) :
    0 ≤ mismatchEnergy weight circleModulus piConstant := by
  unfold mismatchEnergy
  exact mul_nonneg hWeight (sq_nonneg _)

/-- With strictly positive weight, zero energy is exactly spectral isotropy. -/
theorem mismatch_energy_zero_iff_isotropy
    (weight circleModulus piConstant : ℝ)
    (hWeight : 0 < weight) :
    mismatchEnergy weight circleModulus piConstant = 0 ↔
      circleModulus ^ 2 = 2 * piConstant ^ 2 := by
  constructor
  · intro hZero
    unfold mismatchEnergy at hZero
    have hWeightNonzero : weight ≠ 0 := ne_of_gt hWeight
    have hSquare : clearedModeMismatch circleModulus piConstant ^ 2 = 0 :=
      (mul_eq_zero.mp hZero).resolve_left hWeightNonzero
    have hMismatch : clearedModeMismatch circleModulus piConstant = 0 := by
      nlinarith [hSquare]
    unfold clearedModeMismatch at hMismatch
    linarith
  · intro hIsotropy
    unfold mismatchEnergy clearedModeMismatch
    rw [hIsotropy]
    ring

/-- Positive moduli satisfying isotropy are unique. -/
theorem positive_isotropic_modulus_unique
    (t₁ t₂ piConstant : ℝ)
    (hT₁ : 0 < t₁)
    (hT₂ : 0 < t₂)
    (h₁ : t₁ ^ 2 = 2 * piConstant ^ 2)
    (h₂ : t₂ ^ 2 = 2 * piConstant ^ 2) :
    t₁ = t₂ := by
  have hSquares : t₁ ^ 2 = t₂ ^ 2 := h₁.trans h₂.symm
  have hFactor : (t₁ - t₂) * (t₁ + t₂) = 0 := by
    nlinarith [hSquares]
  rcases mul_eq_zero.mp hFactor with hDifference | hSum
  · linarith
  · have hPositive : 0 < t₁ + t₂ := add_pos hT₁ hT₂
    exact False.elim ((ne_of_gt hPositive) hSum)

/--
If the renormalized world-volume action contains this term with positive
coefficient and no competing modulus-dependent term shifts the minimum, the
spectral-isotropy law is a unique vacuum condition rather than a normalization
chosen by hand.
-/
structure SpectralVacuumDerivationStatus where
  spectralOperatorDerived : Prop
  sphereAndCircleModesIdentified : Prop
  positiveMismatchTermComputed : Prop
  competingTermsControlled : Prop
  uniquePositiveModulusProved : Prop
  vacuumGaugeIndependent : Prop
  vacuumSchemeIndependent : Prop


def spectralVacuumDerived (s : SpectralVacuumDerivationStatus) : Prop :=
  s.spectralOperatorDerived /\
  s.sphereAndCircleModesIdentified /\
  s.positiveMismatchTermComputed /\
  s.competingTermsControlled /\
  s.uniquePositiveModulusProved /\
  s.vacuumGaugeIndependent /\
  s.vacuumSchemeIndependent

end P0EFTJanusSpectralMismatchVacuum
end JanusFormal

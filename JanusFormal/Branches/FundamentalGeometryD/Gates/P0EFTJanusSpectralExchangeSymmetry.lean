import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusSpectralMismatchVacuum

namespace JanusFormal
namespace P0EFTJanusSpectralExchangeSymmetry

set_option autoImplicit false

open P0EFTJanusSpectralMismatchVacuum

/-- Most general quadratic effective potential in the cleared first-mode mismatch. -/
def biasedMismatchPotential
    (weight bias constant mismatch : ℝ) : ℝ :=
  weight * mismatch ^ 2 + bias * mismatch + constant

/-- Reflection of the mismatch exchanges the two sides of the putative spectral lock. -/
theorem mismatch_reflection_formula
    (weight bias constant mismatch : ℝ) :
    biasedMismatchPotential weight bias constant (-mismatch) =
      weight * mismatch ^ 2 - bias * mismatch + constant := by
  unfold biasedMismatchPotential
  ring

/-- Exact evenness under `mismatch ↦ -mismatch` forces the linear bias to vanish. -/
theorem exchange_symmetry_forces_zero_bias
    (weight bias constant : ℝ)
    (hEven : ∀ mismatch : ℝ,
      biasedMismatchPotential weight bias constant (-mismatch) =
        biasedMismatchPotential weight bias constant mismatch) :
    bias = 0 := by
  have hOne := hEven 1
  unfold biasedMismatchPotential at hOne
  norm_num at hOne
  linarith

/-- Conversely, zero bias makes the quadratic potential exchange symmetric. -/
theorem zero_bias_gives_exchange_symmetry
    (weight constant : ℝ) :
    ∀ mismatch : ℝ,
      biasedMismatchPotential weight 0 constant (-mismatch) =
        biasedMismatchPotential weight 0 constant mismatch := by
  intro mismatch
  unfold biasedMismatchPotential
  ring

/-- With positive weight and zero bias, mismatch zero is a global minimum. -/
theorem zero_bias_isotropy_global_minimum
    (weight constant mismatch : ℝ)
    (hWeight : 0 < weight) :
    biasedMismatchPotential weight 0 constant 0 ≤
      biasedMismatchPotential weight 0 constant mismatch := by
  unfold biasedMismatchPotential
  have hSquare : 0 ≤ mismatch ^ 2 := sq_nonneg mismatch
  nlinarith

/-- With positive weight and zero bias, every nonzero mismatch has strictly higher energy. -/
theorem zero_bias_isotropy_unique_minimum
    (weight constant mismatch : ℝ)
    (hWeight : 0 < weight)
    (hMismatch : mismatch ≠ 0) :
    biasedMismatchPotential weight 0 constant 0 <
      biasedMismatchPotential weight 0 constant mismatch := by
  unfold biasedMismatchPotential
  have hSquare : 0 < mismatch ^ 2 := sq_pos_of_ne_zero hMismatch
  nlinarith

/-- The stationary equation for the biased quadratic potential. -/
def biasedStationarityEquation
    (weight bias mismatch : ℝ) : Prop :=
  2 * weight * mismatch + bias = 0

/-- Positive weight gives a unique stationary mismatch. -/
theorem biased_stationary_mismatch_unique
    (weight bias d₁ d₂ : ℝ)
    (hWeight : 0 < weight)
    (h₁ : biasedStationarityEquation weight bias d₁)
    (h₂ : biasedStationarityEquation weight bias d₂) :
    d₁ = d₂ := by
  unfold biasedStationarityEquation at h₁ h₂
  have hNonzero : 2 * weight ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hWeight)
  have hFactor : (2 * weight) * (d₁ - d₂) = 0 := by
    nlinarith
  have hDifference : d₁ - d₂ = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hNonzero
  linarith

/-- Isotropy is stationary exactly when the odd bias vanishes. -/
theorem isotropy_stationary_iff_zero_bias
    (weight bias : ℝ) :
    biasedStationarityEquation weight bias 0 ↔ bias = 0 := by
  unfold biasedStationarityEquation
  norm_num

/--
Therefore the spectral-isotropy law is not generic. It requires a derived
exchange/reflection symmetry, anomaly cancellation, or another theorem that
forbids every odd term in the mode mismatch.
-/
structure SpectralExchangeDerivationStatus where
  renormalizedPotentialComputed : Prop
  mismatchCoordinateDerived : Prop
  exchangeSymmetryDerived : Prop
  oddTermsForbiddenToAllOrders : Prop
  positiveQuadraticWeightDerived : Prop
  competingEvenTermsControlled : Prop
  isotropicVacuumUnique : Prop


def spectralExchangeVacuumClosed
    (s : SpectralExchangeDerivationStatus) : Prop :=
  s.renormalizedPotentialComputed /\
  s.mismatchCoordinateDerived /\
  s.exchangeSymmetryDerived /\
  s.oddTermsForbiddenToAllOrders /\
  s.positiveQuadraticWeightDerived /\
  s.competingEvenTermsControlled /\
  s.isotropicVacuumUnique

end P0EFTJanusSpectralExchangeSymmetry
end JanusFormal

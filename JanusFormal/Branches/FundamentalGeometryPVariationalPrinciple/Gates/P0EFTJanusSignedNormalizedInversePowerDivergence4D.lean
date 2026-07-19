import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteMonomialLeadingValuation4D

/-! # Signed divergence of a normalized leading term times an inverse power -/

namespace JanusFormal
namespace P0EFTJanusSignedNormalizedInversePowerDivergence4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

private theorem inversePositivePower_tendsto_atTop {power : Nat} (hPower : 0 < power) :
    Tendsto (fun t : Real => (t ^ power)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
  tendsto_inv_nhdsGT_zero.comp (positivePower_tendsto_zeroWithin hPower)

/-- A normalized factor with a positive nonzero limit preserves the positive
divergence of every inverse power. -/
theorem normalized_mul_inversePower_tendsto_atTop
    (normalized : Real → Real) {coefficient : Real}
    (hNormalized : Tendsto normalized (nhdsWithin 0 (Set.Ioi 0))
      (nhds coefficient)) (hCoefficient : 0 < coefficient)
    {power : Nat} (hPower : 0 < power) :
    Tendsto (fun t => normalized t * (t ^ power)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hInv := inversePositivePower_tendsto_atTop hPower
  have hLower : Tendsto (fun t : Real => (coefficient / 2) * (t ^ power)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    hInv.const_mul_atTop (half_pos hCoefficient)
  apply tendsto_atTop_mono' (nhdsWithin 0 (Set.Ioi 0)) _ hLower
  filter_upwards
    [hNormalized.eventually (eventually_ge_nhds (half_lt_self hCoefficient)),
      self_mem_nhdsWithin] with t hNorm ht
  have hInvNonneg : 0 ≤ (t ^ power)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (le_of_lt ht) power)
  exact mul_le_mul_of_nonneg_right hNorm hInvNonneg

/-- A normalized factor with a negative nonzero limit reverses the same
inverse-power divergence to `-∞`. -/
theorem normalized_mul_inversePower_tendsto_atBot
    (normalized : Real → Real) {coefficient : Real}
    (hNormalized : Tendsto normalized (nhdsWithin 0 (Set.Ioi 0))
      (nhds coefficient)) (hCoefficient : coefficient < 0)
    {power : Nat} (hPower : 0 < power) :
    Tendsto (fun t => normalized t * (t ^ power)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
  have hPositive : Tendsto (fun t => (-normalized t) * (t ^ power)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    normalized_mul_inversePower_tendsto_atTop (fun t => -normalized t)
      (by simpa using hNormalized.neg) (neg_pos.mpr hCoefficient) hPower
  have hNeg := tendsto_neg_atTop_atBot.comp hPositive
  apply hNeg.congr'
  filter_upwards with t
  change -((-normalized t) * (t ^ power)⁻¹) = _
  ring

/-- Therefore either sign of a nonzero normalized leading coefficient rules
out every finite limit after multiplication by a strictly negative valuation.
-/
theorem normalized_mul_inversePower_no_finite_limit
    (normalized : Real → Real) {coefficient : Real}
    (hNormalized : Tendsto normalized (nhdsWithin 0 (Set.Ioi 0))
      (nhds coefficient)) (hCoefficient : coefficient ≠ 0)
    {power : Nat} (hPower : 0 < power) (candidate : Real) :
    ¬ Tendsto (fun t => normalized t * (t ^ power)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  intro hFinite
  rcases lt_or_gt_of_ne hCoefficient with hNeg | hPos
  · exact not_tendsto_atBot_of_tendsto_nhds hFinite
      (normalized_mul_inversePower_tendsto_atBot normalized hNormalized hNeg hPower)
  · exact not_tendsto_atTop_of_tendsto_nhds hFinite
      (normalized_mul_inversePower_tendsto_atTop normalized hNormalized hPos hPower)

end
end P0EFTJanusSignedNormalizedInversePowerDivergence4D
end JanusFormal

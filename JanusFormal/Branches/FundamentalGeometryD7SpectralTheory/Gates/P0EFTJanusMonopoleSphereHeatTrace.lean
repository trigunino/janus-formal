import Mathlib.Analysis.SpecificLimits.Normed
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusGlobalSeparatedDiracModel

namespace JanusFormal
namespace P0EFTJanusMonopoleSphereHeatTrace

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel

noncomputable section

def sphereHeatTerm (data : ProductThroatSpectralData)
    (heatTime : ℝ) (level : ℕ) : ℝ :=
  (sphereMultiplicity data level : ℝ) *
    Real.exp (-heatTime * sphereEigenvalueSquared data level)

def sphereHeatTrace (data : ProductThroatSpectralData) (heatTime : ℝ) : ℝ :=
  ∑' level, sphereHeatTerm data heatTime level

theorem sphere_eigenvalue_linear_lower_bound
    (data : ProductThroatSpectralData) (level : ℕ) :
    ((level + 1 : ℕ) : ℝ) / data.sphereRadius ^ 2 ≤
      sphereEigenvalueSquared data level := by
  unfold sphereEigenvalueSquared monopoleAbsCharge
  have hLevel : (1 : ℝ) ≤ ((level + 1 : ℕ) : ℝ) := by norm_num
  have hCharge : 0 ≤ ((data.monopoleCharge.natAbs : ℕ) : ℝ) := by positivity
  have hRadius : 0 < data.sphereRadius ^ 2 := sq_pos_of_pos data.sphereRadiusPositive
  apply (div_le_div_iff_of_pos_right hRadius).2
  push_cast
  nlinarith

theorem sphere_heat_term_nonnegative
    (data : ProductThroatSpectralData) (heatTime : ℝ) (level : ℕ) :
    0 ≤ sphereHeatTerm data heatTime level := by
  unfold sphereHeatTerm
  positivity

theorem sphere_heat_term_geometric_bound
    (data : ProductThroatSpectralData) (heatTime : ℝ)
    (hHeatTime : 0 < heatTime) (level : ℕ) :
    sphereHeatTerm data heatTime level ≤
      (sphereMultiplicity data level : ℝ) *
        Real.exp (-(heatTime / data.sphereRadius ^ 2) *
          ((level + 1 : ℕ) : ℝ)) := by
  have hEigen := sphere_eigenvalue_linear_lower_bound data level
  have hExponent :
      -heatTime * sphereEigenvalueSquared data level ≤
        -(heatTime / data.sphereRadius ^ 2) *
          ((level + 1 : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hEigen hHeatTime.le
    calc
      -heatTime * sphereEigenvalueSquared data level ≤
          -(heatTime * (((level + 1 : ℕ) : ℝ) / data.sphereRadius ^ 2)) :=
        by simpa [neg_mul] using neg_le_neg this
      _ = -(heatTime / data.sphereRadius ^ 2) *
          ((level + 1 : ℕ) : ℝ) := by ring
  unfold sphereHeatTerm
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExponent) (by positivity)

theorem sphere_heat_trace_summable
    (data : ProductThroatSpectralData) (heatTime : ℝ)
    (hHeatTime : 0 < heatTime) :
    Summable (sphereHeatTerm data heatTime) := by
  let ratio : ℝ := Real.exp (-(heatTime / data.sphereRadius ^ 2))
  have hScaled : 0 < heatTime / data.sphereRadius ^ 2 :=
    div_pos hHeatTime (sq_pos_of_pos data.sphereRadiusPositive)
  have hDecay : -(heatTime / data.sphereRadius ^ 2) < 0 := neg_neg_of_pos hScaled
  have hRatioNonnegative : 0 ≤ ratio := Real.exp_nonneg _
  have hRatioLessThanOne : ratio < 1 := (Real.exp_lt_one_iff).2 hDecay
  have hGeom : Summable (fun n : ℕ => (n : ℝ) * ratio ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hRatioNonnegative]))
  have hPure : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hRatioNonnegative hRatioLessThanOne
  have hMajorant : Summable (fun level : ℕ =>
      (sphereMultiplicity data level : ℝ) * ratio ^ (level + 1)) := by
    unfold sphereMultiplicity monopoleAbsCharge
    simp_rw [pow_succ]
    push_cast
    ring_nf
    exact ((hPure.mul_left
      ((data.monopoleCharge.natAbs : ℝ) * ratio + 2 * ratio)).add
        (hGeom.mul_left (2 * ratio))).congr (by intro n; ring)
  refine hMajorant.of_nonneg_of_le (sphere_heat_term_nonnegative data heatTime) ?_
  intro level
  refine (sphere_heat_term_geometric_bound data heatTime hHeatTime level).trans_eq ?_
  unfold ratio
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem sphere_heat_trace_has_sum
    (data : ProductThroatSpectralData) (heatTime : ℝ)
    (hHeatTime : 0 < heatTime) :
    HasSum (sphereHeatTerm data heatTime) (sphereHeatTrace data heatTime) :=
  (sphere_heat_trace_summable data heatTime hHeatTime).hasSum

end

end P0EFTJanusMonopoleSphereHeatTrace
end JanusFormal

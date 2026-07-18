import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyDerivative4D

/-!
# Lipschitz derivative of the product-throat holonomy family

The second holonomy derivative is explicit and uniformly bounded by the
inverse sphere gap.  The mean-value theorem then makes the first derivative
multiplier Lipschitz in operator norm.  This is the quantitative regularity
needed before promoting the common-domain spectral family to a norm-smooth
graph-domain family.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyDerivativeLipschitz4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open scoped ENNReal lp

/-- Exact second holonomy derivative coefficient. -/
def productThroatDiracHolonomySecondDerivativeCoefficient
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) : ℝ :=
  fold.spectralSign * sphereEigenvalueSquared data mode.1.1 /
    (productThroatDiracSquaredEigenvalueAt data holonomy mode *
      Real.sqrt (productThroatDiracSquaredEigenvalueAt data holonomy mode))

private theorem shifted_hasDerivAt
    (mode : ℤ) (holonomy : ℝ) :
    HasDerivAt (fun parameter : ℝ => (mode : ℝ) + parameter) 1 holonomy := by
  rw [show (fun parameter : ℝ => (mode : ℝ) + parameter) =
    fun parameter : ℝ => parameter + (mode : ℝ) by
      funext parameter
      exact add_comm _ _]
  rw [hasDerivAt_add_const_iff]
  exact hasDerivAt_id holonomy

theorem productThroatDiracHolonomyDerivativeCoefficient_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    HasDerivAt
      (fun parameter => productThroatDiracHolonomyDerivativeCoefficient
        data fold parameter mode)
      (productThroatDiracHolonomySecondDerivativeCoefficient
        data fold holonomy mode) holonomy := by
  let shifted : ℝ → ℝ := fun parameter => (mode.2 : ℝ) + parameter
  let energy : ℝ → ℝ := fun parameter =>
    sphereEigenvalueSquared data mode.1.1 + shifted parameter ^ 2
  have hShifted : HasDerivAt shifted 1 holonomy :=
    shifted_hasDerivAt mode.2 holonomy
  have hEnergy : HasDerivAt energy (2 * shifted holonomy) holonomy := by
    let raw : ℝ → ℝ :=
      (fun _ => sphereEigenvalueSquared data mode.1.1) + shifted ^ 2
    have hRawBase := (hasDerivAt_const holonomy
      (sphereEigenvalueSquared data mode.1.1)).add (hShifted.pow 2)
    have hRaw : HasDerivAt raw (2 * shifted holonomy) holonomy := by
      apply hRawBase.congr_deriv
      norm_num
    apply hRaw.congr_of_eventuallyEq
    filter_upwards with parameter
    rfl
  have hEnergyPositive : 0 < energy holonomy := by
    exact add_pos_of_pos_of_nonneg
      (sphere_eigenvalue_squared_positive data mode.1.1) (sq_nonneg _)
  have hSqrtBase := hEnergy.sqrt (ne_of_gt hEnergyPositive)
  have hSqrt : HasDerivAt (fun parameter => Real.sqrt (energy parameter))
      (shifted holonomy / Real.sqrt (energy holonomy)) holonomy := by
    apply hSqrtBase.congr_deriv
    field_simp [ne_of_gt (Real.sqrt_pos.2 hEnergyPositive)]
  have hQuotient := hShifted.div hSqrt
    (ne_of_gt (Real.sqrt_pos.2 hEnergyPositive))
  have hScaled := hQuotient.const_mul fold.spectralSign
  have hQuotientDerivative :
      (1 * Real.sqrt (energy holonomy) -
          shifted holonomy *
            (shifted holonomy / Real.sqrt (energy holonomy))) /
        Real.sqrt (energy holonomy) ^ 2 =
      sphereEigenvalueSquared data mode.1.1 /
        (energy holonomy * Real.sqrt (energy holonomy)) := by
    have hSqrtSq : Real.sqrt (energy holonomy) ^ 2 = energy holonomy :=
      Real.sq_sqrt hEnergyPositive.le
    field_simp [ne_of_gt (Real.sqrt_pos.2 hEnergyPositive)]
    rw [hSqrtSq]
    dsimp only [energy]
    ring
  have hSecond :
      fold.spectralSign *
          ((1 * Real.sqrt (energy holonomy) -
              shifted holonomy *
                (shifted holonomy / Real.sqrt (energy holonomy))) /
            Real.sqrt (energy holonomy) ^ 2) =
        productThroatDiracHolonomySecondDerivativeCoefficient
          data fold holonomy mode := by
    rw [hQuotientDerivative]
    unfold productThroatDiracHolonomySecondDerivativeCoefficient
    dsimp only [energy, productThroatDiracSquaredEigenvalueAt]
    ring
  have hScaled' := hScaled.congr_deriv hSecond
  apply hScaled'.congr_of_eventuallyEq
  filter_upwards with parameter
  change fold.spectralSign * ((mode.2 : ℝ) + parameter) /
      Real.sqrt (productThroatDiracSquaredEigenvalueAt data parameter mode) =
    fold.spectralSign *
      (shifted parameter / Real.sqrt (energy parameter))
  rw [show productThroatDiracSquaredEigenvalueAt data parameter mode =
      energy parameter by rfl]
  change fold.spectralSign * shifted parameter / Real.sqrt (energy parameter) =
    fold.spectralSign * (shifted parameter / Real.sqrt (energy parameter))
  ring

theorem productThroatDiracHolonomySecondDerivativeCoefficient_abs_le_gap_inv
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    |productThroatDiracHolonomySecondDerivativeCoefficient
        data fold holonomy mode| ≤ (productThroatDiracGap data)⁻¹ := by
  let sphere := sphereEigenvalueSquared data mode.1.1
  let energy := productThroatDiracSquaredEigenvalueAt data holonomy mode
  have hSphere : 0 < sphere := sphere_eigenvalue_squared_positive data mode.1.1
  have hEnergy : 0 < energy :=
    productThroatDiracSquaredEigenvalueAt_positive data holonomy mode
  have hSphereEnergy : sphere ≤ energy := by
    dsimp [sphere, energy, productThroatDiracSquaredEigenvalueAt]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hGapSqrt : productThroatDiracGap data ≤ Real.sqrt energy := by
    apply Real.sqrt_le_sqrt
    exact le_trans (sphereEigenvalueSquared_zero_le data mode.1.1) hSphereEnergy
  rw [productThroatDiracHolonomySecondDerivativeCoefficient, abs_div, abs_mul]
  have hSign : |fold.spectralSign| = 1 := by cases fold <;> norm_num
  rw [hSign, one_mul, abs_of_pos hSphere, abs_mul,
    abs_of_pos hEnergy, abs_of_pos (Real.sqrt_pos.2 hEnergy)]
  have hFraction : sphere / energy ≤ 1 := (div_le_one hEnergy).2 hSphereEnergy
  calc
    sphere / (energy * Real.sqrt energy) =
        (sphere / energy) * (Real.sqrt energy)⁻¹ := by field_simp
    _ ≤ 1 * (Real.sqrt energy)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hFraction (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (Real.sqrt energy)⁻¹ := one_mul _
    _ ≤ (productThroatDiracGap data)⁻¹ :=
      inv_anti₀ (productThroatDiracGap_positive data) hGapSqrt

theorem productThroatDiracHolonomyDerivativeCoefficient_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) (mode : ProductThroatHeatMode data) :
    |productThroatDiracHolonomyDerivativeCoefficient data fold second mode -
        productThroatDiracHolonomyDerivativeCoefficient data fold first mode| ≤
      (productThroatDiracGap data)⁻¹ * |second - first| := by
  have hMVT := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ))
    (f := fun parameter => productThroatDiracHolonomyDerivativeCoefficient
      data fold parameter mode)
    (f' := fun parameter => productThroatDiracHolonomySecondDerivativeCoefficient
      data fold parameter mode)
    (C := (productThroatDiracGap data)⁻¹)
    (fun parameter _ =>
      (productThroatDiracHolonomyDerivativeCoefficient_hasDerivAt
        data fold parameter mode).hasDerivWithinAt)
    (fun parameter _ => by
      rw [Real.norm_eq_abs]
      exact productThroatDiracHolonomySecondDerivativeCoefficient_abs_le_gap_inv
        data fold parameter mode)
    (Set.mem_univ first) (Set.mem_univ second)
  simpa [Real.norm_eq_abs] using hMVT

theorem productThroatDiracHolonomyDerivativeOperator_sub_norm_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) :
    ‖productThroatDiracHolonomyDerivativeOperator data fold second -
        productThroatDiracHolonomyDerivativeOperator data fold first‖ ≤
      (productThroatDiracGap data)⁻¹ * |second - first| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (inv_nonneg.mpr (productThroatDiracGap_positive data).le)
      (abs_nonneg _)
  · intro state
    calc
      ‖(productThroatDiracHolonomyDerivativeOperator data fold second -
          productThroatDiracHolonomyDerivativeOperator data fold first) state‖ =
          ‖productThroatDiracHolonomyDerivativeImage data fold second state -
            productThroatDiracHolonomyDerivativeImage data fold first state‖ := rfl
      _ ≤ ‖(((productThroatDiracGap data)⁻¹ * |second - first| : ℝ) : Complex) •
          state‖ := lp.norm_mono (by norm_num) (fun mode => by
            change ‖(productThroatDiracHolonomyDerivativeCoefficient
                data fold second mode : Complex) * state mode -
              (productThroatDiracHolonomyDerivativeCoefficient
                data fold first mode : Complex) * state mode‖ ≤
              ‖(((productThroatDiracGap data)⁻¹ * |second - first| : ℝ) : Complex) *
                state mode‖
            rw [← sub_mul]
            rw [← Complex.ofReal_sub]
            rw [norm_mul, norm_mul, Complex.norm_real,
              Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg
                (inv_nonneg.mpr (productThroatDiracGap_positive data).le)
                (abs_nonneg _))]
            exact mul_le_mul_of_nonneg_right
              (productThroatDiracHolonomyDerivativeCoefficient_lipschitz
                data fold first second mode) (norm_nonneg _))
      _ = ((productThroatDiracGap data)⁻¹ * |second - first|) * ‖state‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg
            (inv_nonneg.mpr (productThroatDiracGap_positive data).le)
            (abs_nonneg _))]

end

end P0EFTJanusProductThroatHolonomyDerivativeLipschitz4D
end JanusFormal

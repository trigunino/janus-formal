import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyDerivativeLipschitz4D

/-!
# Second operator derivative of the product-throat holonomy family

The third scalar derivative is explicit and uniformly bounded.  This first
gives a uniform Taylor control for the second spectral coefficient, before
assembling the corresponding diagonal operator.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomySecondDerivative4D

set_option autoImplicit false

noncomputable section

open Asymptotics Filter
open Set
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open P0EFTJanusProductThroatHolonomyDerivativeLipschitz4D
open scoped ENNReal lp

/-- Exact third holonomy derivative coefficient. -/
def productThroatDiracHolonomyThirdDerivativeCoefficient
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) : ℝ :=
  -3 * fold.spectralSign * sphereEigenvalueSquared data mode.1.1 *
      ((mode.2 : ℝ) + holonomy) /
    (productThroatDiracSquaredEigenvalueAt data holonomy mode ^ 2 *
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

theorem productThroatDiracHolonomySecondDerivativeCoefficient_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    HasDerivAt
      (fun parameter => productThroatDiracHolonomySecondDerivativeCoefficient
        data fold parameter mode)
      (productThroatDiracHolonomyThirdDerivativeCoefficient
        data fold holonomy mode) holonomy := by
  let shifted : ℝ → ℝ := fun parameter => (mode.2 : ℝ) + parameter
  let energy : ℝ → ℝ := fun parameter =>
    sphereEigenvalueSquared data mode.1.1 + shifted parameter ^ 2
  let denominator : ℝ → ℝ := fun parameter =>
    energy parameter * Real.sqrt (energy parameter)
  let numerator : ℝ :=
    fold.spectralSign * sphereEigenvalueSquared data mode.1.1
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
  have hSqrt : HasDerivAt (fun parameter => Real.sqrt (energy parameter))
      (shifted holonomy / Real.sqrt (energy holonomy)) holonomy := by
    have hRaw := hEnergy.sqrt (ne_of_gt hEnergyPositive)
    convert hRaw using 1
    field_simp [ne_of_gt (Real.sqrt_pos.2 hEnergyPositive)]
  have hDenominator : HasDerivAt denominator
      (2 * shifted holonomy * Real.sqrt (energy holonomy) +
        energy holonomy *
          (shifted holonomy / Real.sqrt (energy holonomy))) holonomy := by
    have hRaw := hEnergy.mul hSqrt
    apply hRaw.congr_of_eventuallyEq
    filter_upwards with parameter
    rfl
  have hQuotient := (hasDerivAt_const holonomy numerator).div hDenominator
    (mul_ne_zero (ne_of_gt hEnergyPositive)
      (ne_of_gt (Real.sqrt_pos.2 hEnergyPositive)))
  have hDerivative :
      (0 * denominator holonomy - numerator *
          (2 * shifted holonomy * Real.sqrt (energy holonomy) +
            energy holonomy *
              (shifted holonomy / Real.sqrt (energy holonomy)))) /
        denominator holonomy ^ 2 =
      productThroatDiracHolonomyThirdDerivativeCoefficient
        data fold holonomy mode := by
    have hSqrtSq : Real.sqrt (energy holonomy) ^ 2 = energy holonomy :=
      Real.sq_sqrt hEnergyPositive.le
    have hDenominatorDerivative :
        2 * shifted holonomy * Real.sqrt (energy holonomy) +
            energy holonomy *
              (shifted holonomy / Real.sqrt (energy holonomy)) =
          3 * shifted holonomy * Real.sqrt (energy holonomy) := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 hEnergyPositive)]
      rw [hSqrtSq]
      ring
    rw [hDenominatorDerivative]
    unfold productThroatDiracHolonomyThirdDerivativeCoefficient
    dsimp only [denominator, numerator]
    change
      (0 * (energy holonomy * Real.sqrt (energy holonomy)) -
          fold.spectralSign * sphereEigenvalueSquared data mode.1.1 *
            (3 * shifted holonomy * Real.sqrt (energy holonomy))) /
        (energy holonomy * Real.sqrt (energy holonomy)) ^ 2 =
      -3 * fold.spectralSign * sphereEigenvalueSquared data mode.1.1 *
          shifted holonomy /
        (energy holonomy ^ 2 * Real.sqrt (energy holonomy))
    field_simp [ne_of_gt hEnergyPositive,
      ne_of_gt (Real.sqrt_pos.2 hEnergyPositive)]
    ring
  have hExact := hQuotient.congr_deriv hDerivative
  apply hExact.congr_of_eventuallyEq
  filter_upwards with parameter
  rfl

theorem productThroatDiracHolonomyThirdDerivativeCoefficient_abs_le
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    |productThroatDiracHolonomyThirdDerivativeCoefficient
        data fold holonomy mode| ≤
      3 * (productThroatDiracGap data ^ 2)⁻¹ := by
  let sphere := sphereEigenvalueSquared data mode.1.1
  let shifted : ℝ := (mode.2 : ℝ) + holonomy
  let energy := productThroatDiracSquaredEigenvalueAt data holonomy mode
  have hSphere : 0 < sphere :=
    sphere_eigenvalue_squared_positive data mode.1.1
  have hEnergy : 0 < energy :=
    productThroatDiracSquaredEigenvalueAt_positive data holonomy mode
  have hEnergyEq : energy = sphere + shifted ^ 2 := rfl
  have hSphereEnergy : sphere ≤ energy := by
    rw [hEnergyEq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hShiftedSqrt : |shifted| ≤ Real.sqrt energy := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by
      rw [hEnergyEq]
      exact le_add_of_nonneg_left hSphere.le)
  have hGapSqEnergy : productThroatDiracGap data ^ 2 ≤ energy := by
    rw [productThroatDiracGap,
      Real.sq_sqrt (sphere_eigenvalue_squared_positive data 0).le]
    exact le_trans (sphereEigenvalueSquared_zero_le data mode.1.1) hSphereEnergy
  have hNumerator : 3 * sphere * |shifted| ≤
      3 * energy * Real.sqrt energy := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hSphereEnergy (by norm_num))
      hShiftedSqrt (abs_nonneg shifted)
      (mul_nonneg (by norm_num) hEnergy.le)
  rw [productThroatDiracHolonomyThirdDerivativeCoefficient,
    abs_div, abs_mul, abs_mul, abs_mul]
  have hSign : |fold.spectralSign| = 1 := by cases fold <;> norm_num
  rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), hSign,
    mul_one, abs_of_pos hSphere, abs_mul,
    abs_of_pos (pow_pos hEnergy 2),
    abs_of_pos (Real.sqrt_pos.2 hEnergy)]
  change 3 * sphere * |shifted| / (energy ^ 2 * Real.sqrt energy) ≤ _
  calc
    3 * sphere * |shifted| / (energy ^ 2 * Real.sqrt energy) ≤
        (3 * energy * Real.sqrt energy) /
          (energy ^ 2 * Real.sqrt energy) :=
      div_le_div_of_nonneg_right hNumerator
        (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    _ = 3 * energy⁻¹ := by
      field_simp [ne_of_gt hEnergy, ne_of_gt (Real.sqrt_pos.2 hEnergy)]
    _ ≤ 3 * (productThroatDiracGap data ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (sq_pos_of_pos (productThroatDiracGap_positive data))
          hGapSqEnergy) (by norm_num)
    _ = 3 * (productThroatDiracGap data ^ 2)⁻¹ := rfl

theorem productThroatDiracHolonomySecondDerivativeCoefficient_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) (mode : ProductThroatHeatMode data) :
    |productThroatDiracHolonomySecondDerivativeCoefficient
        data fold second mode -
      productThroatDiracHolonomySecondDerivativeCoefficient
        data fold first mode| ≤
      (3 * (productThroatDiracGap data ^ 2)⁻¹) * |second - first| := by
  have hMVT := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ))
    (f := fun parameter => productThroatDiracHolonomySecondDerivativeCoefficient
      data fold parameter mode)
    (f' := fun parameter => productThroatDiracHolonomyThirdDerivativeCoefficient
      data fold parameter mode)
    (C := 3 * (productThroatDiracGap data ^ 2)⁻¹)
    (fun parameter _ =>
      (productThroatDiracHolonomySecondDerivativeCoefficient_hasDerivAt
        data fold parameter mode).hasDerivWithinAt)
    (fun parameter _ => by
      rw [Real.norm_eq_abs]
      exact productThroatDiracHolonomyThirdDerivativeCoefficient_abs_le
        data fold parameter mode)
    (Set.mem_univ first) (Set.mem_univ second)
  simpa [Real.norm_eq_abs] using hMVT

/-- Bounded diagonal second-derivative multiplier on the product Hilbert space. -/
def productThroatDiracHolonomySecondDerivativeImage
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) : ProductThroatHeatHilbert data := by
  let secondDerivative : ProductThroatHeatMode data → Complex := fun mode =>
    (productThroatDiracHolonomySecondDerivativeCoefficient
      data fold holonomy mode : Complex) * state mode
  have hScaled : Memℓp (fun mode =>
      (((productThroatDiracGap data)⁻¹ : ℝ) : Complex) * state mode) 2 :=
    (lp.memℓp state).const_mul (((productThroatDiracGap data)⁻¹ : ℝ) : Complex)
  have hSecondDerivative : Memℓp secondDerivative 2 :=
    hScaled.mono' (fun mode => by
      change ‖(productThroatDiracHolonomySecondDerivativeCoefficient
          data fold holonomy mode : Complex) * state mode‖ ≤
        ‖(((productThroatDiracGap data)⁻¹ : ℝ) : Complex) * state mode‖
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (productThroatDiracGap_positive data).le)]
      exact mul_le_mul_of_nonneg_right
        (productThroatDiracHolonomySecondDerivativeCoefficient_abs_le_gap_inv
          data fold holonomy mode) (norm_nonneg _))
  exact ⟨secondDerivative, hSecondDerivative⟩

@[simp] theorem productThroatDiracHolonomySecondDerivativeImage_apply
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracHolonomySecondDerivativeImage
        data fold holonomy state mode =
      (productThroatDiracHolonomySecondDerivativeCoefficient
        data fold holonomy mode : Complex) * state mode :=
  rfl

theorem productThroatDiracHolonomySecondDerivativeImage_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) :
    ‖productThroatDiracHolonomySecondDerivativeImage
      data fold holonomy state‖ ≤
      (productThroatDiracGap data)⁻¹ * ‖state‖ := by
  calc
    _ ≤ ‖(((productThroatDiracGap data)⁻¹ : ℝ) : Complex) • state‖ :=
      lp.norm_mono (by norm_num) (fun mode => by
        change ‖(productThroatDiracHolonomySecondDerivativeCoefficient
            data fold holonomy mode : Complex) * state mode‖ ≤
          ‖(((productThroatDiracGap data)⁻¹ : ℝ) : Complex) * state mode‖
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (productThroatDiracGap_positive data).le)]
        exact mul_le_mul_of_nonneg_right
          (productThroatDiracHolonomySecondDerivativeCoefficient_abs_le_gap_inv
            data fold holonomy mode) (norm_nonneg _))
    _ = (productThroatDiracGap data)⁻¹ * ‖state‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (productThroatDiracGap_positive data).le)]

/-- Bounded second derivative operator. -/
def productThroatDiracHolonomySecondDerivativeOperator
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  LinearMap.mkContinuous
    { toFun := productThroatDiracHolonomySecondDerivativeImage data fold holonomy
      map_add' := by
        intro first second
        ext mode
        simp [productThroatDiracHolonomySecondDerivativeImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [productThroatDiracHolonomySecondDerivativeImage_apply]
        ring }
    (productThroatDiracGap data)⁻¹
    (fun state => productThroatDiracHolonomySecondDerivativeImage_norm_le
      data fold holonomy state)

theorem productThroatDiracHolonomySecondDerivativeOperator_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ) :
    ‖productThroatDiracHolonomySecondDerivativeOperator
      data fold holonomy‖ ≤ (productThroatDiracGap data)⁻¹ := by
  apply LinearMap.mkContinuous_norm_le
  exact inv_nonneg.mpr (productThroatDiracGap_positive data).le

@[simp] theorem productThroatDiracHolonomyDerivativeOperator_apply
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) :
    productThroatDiracHolonomyDerivativeOperator data fold holonomy state =
      productThroatDiracHolonomyDerivativeImage data fold holonomy state :=
  rfl

@[simp] theorem productThroatDiracHolonomySecondDerivativeOperator_apply
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) :
    productThroatDiracHolonomySecondDerivativeOperator data fold holonomy state =
      productThroatDiracHolonomySecondDerivativeImage data fold holonomy state :=
  rfl

theorem productThroatDiracHolonomyDerivativeCoefficient_taylor_remainder_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) (mode : ProductThroatHeatMode data) :
    |productThroatDiracHolonomyDerivativeCoefficient data fold second mode -
        productThroatDiracHolonomyDerivativeCoefficient data fold first mode -
        productThroatDiracHolonomySecondDerivativeCoefficient data fold first mode *
          (second - first)| ≤
      (3 * (productThroatDiracGap data ^ 2)⁻¹) * |second - first| ^ 2 := by
  let adjusted : ℝ → ℝ := fun parameter =>
    productThroatDiracHolonomyDerivativeCoefficient data fold parameter mode -
      productThroatDiracHolonomySecondDerivativeCoefficient data fold first mode * parameter
  have hDerivative : ∀ parameter : ℝ,
      HasDerivAt adjusted
        (productThroatDiracHolonomySecondDerivativeCoefficient
            data fold parameter mode -
          productThroatDiracHolonomySecondDerivativeCoefficient
            data fold first mode) parameter := by
    intro parameter
    have hRaw :=
      (productThroatDiracHolonomyDerivativeCoefficient_hasDerivAt
        data fold parameter mode).sub
      ((hasDerivAt_id parameter).const_mul
        (productThroatDiracHolonomySecondDerivativeCoefficient
          data fold first mode))
    have hRaw' : HasDerivAt
        ((fun x => productThroatDiracHolonomyDerivativeCoefficient
            data fold x mode) -
          fun x => productThroatDiracHolonomySecondDerivativeCoefficient
            data fold first mode * x)
        (productThroatDiracHolonomySecondDerivativeCoefficient
            data fold parameter mode -
          productThroatDiracHolonomySecondDerivativeCoefficient
            data fold first mode) parameter := by
      simpa using hRaw
    apply hRaw'.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have hMVT := (convex_uIcc first second).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := adjusted)
    (f' := fun parameter =>
      productThroatDiracHolonomySecondDerivativeCoefficient
          data fold parameter mode -
        productThroatDiracHolonomySecondDerivativeCoefficient
          data fold first mode)
    (C := (3 * (productThroatDiracGap data ^ 2)⁻¹) * |second - first|)
    (fun parameter _ => (hDerivative parameter).hasDerivWithinAt)
    (fun parameter hParameter => by
      rw [Real.norm_eq_abs]
      exact le_trans
        (productThroatDiracHolonomySecondDerivativeCoefficient_lipschitz
          data fold first parameter mode)
        (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hParameter)
          (mul_nonneg (by norm_num)
            (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))))
    left_mem_uIcc right_mem_uIcc
  calc
    _ = ‖adjusted second - adjusted first‖ := by
      rw [Real.norm_eq_abs]
      congr 1
      simp only [adjusted]
      ring
    _ ≤ (3 * (productThroatDiracGap data ^ 2)⁻¹) *
          |second - first| * ‖second - first‖ := hMVT
    _ = (3 * (productThroatDiracGap data ^ 2)⁻¹) *
          |second - first| ^ 2 := by
      rw [Real.norm_eq_abs]
      ring

theorem productThroatDiracHolonomyDerivativeOperator_taylor_remainder_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) :
    ‖productThroatDiracHolonomyDerivativeOperator data fold second -
        productThroatDiracHolonomyDerivativeOperator data fold first -
        (second - first) •
          productThroatDiracHolonomySecondDerivativeOperator data fold first‖ ≤
      (3 * (productThroatDiracGap data ^ 2)⁻¹) * |second - first| ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
      (sq_nonneg _)
  · intro state
    calc
      ‖(productThroatDiracHolonomyDerivativeOperator data fold second -
          productThroatDiracHolonomyDerivativeOperator data fold first -
          (second - first) •
            productThroatDiracHolonomySecondDerivativeOperator
              data fold first) state‖ ≤
          ‖(((3 * (productThroatDiracGap data ^ 2)⁻¹) *
              |second - first| ^ 2 : ℝ) : Complex) • state‖ :=
        lp.norm_mono (by norm_num) (fun mode => by
          simp only [sub_apply, smul_apply,
            productThroatDiracHolonomyDerivativeOperator_apply,
            productThroatDiracHolonomySecondDerivativeOperator_apply]
          rw [show
            (productThroatDiracHolonomyDerivativeImage data fold second state -
                productThroatDiracHolonomyDerivativeImage data fold first state -
                (second - first) •
                  productThroatDiracHolonomySecondDerivativeImage
                    data fold first state) mode =
              (productThroatDiracHolonomyDerivativeCoefficient
                data fold second mode : Complex) * state mode -
              (productThroatDiracHolonomyDerivativeCoefficient
                data fold first mode : Complex) * state mode -
              ((second - first : ℝ) : Complex) *
                (productThroatDiracHolonomySecondDerivativeCoefficient
                  data fold first mode : Complex) * state mode by
                simp [productThroatDiracHolonomyDerivativeImage_apply,
                  productThroatDiracHolonomySecondDerivativeImage_apply]
                ring,
            show ((((3 * (productThroatDiracGap data ^ 2)⁻¹) *
                |second - first| ^ 2 : ℝ) : Complex) • state) mode =
              (((3 * (productThroatDiracGap data ^ 2)⁻¹) *
                |second - first| ^ 2 : ℝ) : Complex) * state mode by rfl]
          rw [show
            (productThroatDiracHolonomyDerivativeCoefficient
                data fold second mode : Complex) * state mode -
              (productThroatDiracHolonomyDerivativeCoefficient
                data fold first mode : Complex) * state mode -
              ((second - first : ℝ) : Complex) *
                (productThroatDiracHolonomySecondDerivativeCoefficient
                  data fold first mode : Complex) * state mode =
              ((productThroatDiracHolonomyDerivativeCoefficient
                  data fold second mode -
                productThroatDiracHolonomyDerivativeCoefficient
                  data fold first mode -
                productThroatDiracHolonomySecondDerivativeCoefficient
                  data fold first mode * (second - first) : ℝ) : Complex) *
                state mode by
              push_cast
              ring]
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg
              (mul_nonneg (by norm_num)
                (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
              (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right
            (productThroatDiracHolonomyDerivativeCoefficient_taylor_remainder_le
              data fold first second mode) (norm_nonneg _))
      _ = ((3 * (productThroatDiracGap data ^ 2)⁻¹) *
          |second - first| ^ 2) * ‖state‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg
            (mul_nonneg (by norm_num)
              (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
            (sq_nonneg _))]

theorem productThroatDiracHolonomyDerivativeOperator_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ) :
    HasDerivAt
      (fun parameter => productThroatDiracHolonomyDerivativeOperator
        data fold parameter)
      (productThroatDiracHolonomySecondDerivativeOperator data fold holonomy)
      holonomy := by
  apply HasDerivAt.of_isLittleO
  have hBigO :
      (fun parameter =>
        productThroatDiracHolonomyDerivativeOperator data fold parameter -
          productThroatDiracHolonomyDerivativeOperator data fold holonomy -
          (parameter - holonomy) •
            productThroatDiracHolonomySecondDerivativeOperator
              data fold holonomy) =O[nhds holonomy]
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
    have hBound : IsBigOWith
        (3 * (productThroatDiracGap data ^ 2)⁻¹) (nhds holonomy)
        (fun parameter =>
          productThroatDiracHolonomyDerivativeOperator data fold parameter -
            productThroatDiracHolonomyDerivativeOperator data fold holonomy -
            (parameter - holonomy) •
              productThroatDiracHolonomySecondDerivativeOperator
                data fold holonomy)
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
      apply IsBigOWith.of_bound
      filter_upwards with parameter
      simpa only [norm_pow, norm_norm, Real.norm_eq_abs, abs_abs] using
        (productThroatDiracHolonomyDerivativeOperator_taylor_remainder_le
          data fold holonomy parameter)
    exact hBound.isBigO
  exact hBigO.trans_isLittleO
    (isLittleO_pow_sub_sub holonomy (by norm_num : 1 < 2))

theorem productThroatDiracHolonomySecondDerivativeOperator_sub_norm_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) :
    ‖productThroatDiracHolonomySecondDerivativeOperator data fold second -
        productThroatDiracHolonomySecondDerivativeOperator data fold first‖ ≤
      (3 * (productThroatDiracGap data ^ 2)⁻¹) * |second - first| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
      (abs_nonneg _)
  · intro state
    calc
      ‖(productThroatDiracHolonomySecondDerivativeOperator data fold second -
          productThroatDiracHolonomySecondDerivativeOperator
            data fold first) state‖ =
          ‖productThroatDiracHolonomySecondDerivativeImage
              data fold second state -
            productThroatDiracHolonomySecondDerivativeImage
              data fold first state‖ := rfl
      _ ≤ ‖(((3 * (productThroatDiracGap data ^ 2)⁻¹) *
            |second - first| : ℝ) : Complex) • state‖ :=
        lp.norm_mono (by norm_num) (fun mode => by
          change ‖(productThroatDiracHolonomySecondDerivativeCoefficient
                data fold second mode : Complex) * state mode -
              (productThroatDiracHolonomySecondDerivativeCoefficient
                data fold first mode : Complex) * state mode‖ ≤
            ‖(((3 * (productThroatDiracGap data ^ 2)⁻¹) *
                |second - first| : ℝ) : Complex) * state mode‖
          rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, norm_mul,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg
              (mul_nonneg (by norm_num)
                (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
              (abs_nonneg _))]
          exact mul_le_mul_of_nonneg_right
            (productThroatDiracHolonomySecondDerivativeCoefficient_lipschitz
              data fold first second mode) (norm_nonneg _))
      _ = ((3 * (productThroatDiracGap data ^ 2)⁻¹) *
          |second - first|) * ‖state‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg
            (mul_nonneg (by norm_num)
              (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
            (abs_nonneg _))]

theorem productThroatDiracHolonomySecondDerivativeOperator_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold) :
    LipschitzWith
      ⟨3 * (productThroatDiracGap data ^ 2)⁻¹,
        mul_nonneg (by norm_num)
          (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data)))⟩
      (productThroatDiracHolonomySecondDerivativeOperator data fold) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simp only [dist_eq_norm, Real.norm_eq_abs]
  change ‖productThroatDiracHolonomySecondDerivativeOperator data fold first -
      productThroatDiracHolonomySecondDerivativeOperator data fold second‖ ≤
    (3 * (productThroatDiracGap data ^ 2)⁻¹) * |first - second|
  simpa [abs_sub_comm] using
    (productThroatDiracHolonomySecondDerivativeOperator_sub_norm_le
      data fold second first)

end

end P0EFTJanusProductThroatHolonomySecondDerivative4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyDerivativeLipschitz4D
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Norm differentiability of the product-throat holonomy perturbation

The real-holonomy spectral perturbation relative to a fixed reference is a
bounded diagonal operator.  Its quadratic Taylor remainder is uniform in the
mode, hence the family is differentiable in operator norm.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyOperatorDifferentiable4D

set_option autoImplicit false

noncomputable section

open Asymptotics Filter Set
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open P0EFTJanusProductThroatHolonomyDerivativeLipschitz4D
open scoped ENNReal lp

theorem productThroatDiracEigenvalueAt_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) (mode : ProductThroatHeatMode data) :
    |productThroatDiracEigenvalueAt data fold second mode -
        productThroatDiracEigenvalueAt data fold first mode| ≤ |second - first| := by
  have hMVT := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ))
    (f := fun parameter => productThroatDiracEigenvalueAt data fold parameter mode)
    (f' := fun parameter => productThroatDiracHolonomyDerivativeCoefficient
      data fold parameter mode)
    (C := 1)
    (fun parameter _ =>
      (productThroatDiracEigenvalueAt_hasDerivAt
        data fold parameter mode).hasDerivWithinAt)
    (fun parameter _ => by
      rw [Real.norm_eq_abs]
      exact productThroatDiracHolonomyDerivativeCoefficient_abs_le_one
        data fold parameter mode)
    (Set.mem_univ first) (Set.mem_univ second)
  simpa [Real.norm_eq_abs] using hMVT

/-- Bounded diagonal change of the Dirac operator from `reference` to `holonomy`. -/
def productThroatDiracHolonomyPerturbationImage
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference holonomy : ℝ) (state : ProductThroatHeatHilbert data) :
    ProductThroatHeatHilbert data := by
  let perturbation : ProductThroatHeatMode data → Complex := fun mode =>
    ((productThroatDiracEigenvalueAt data fold holonomy mode -
      productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) * state mode
  have hScaled : Memℓp (fun mode =>
      ((|holonomy - reference| : ℝ) : Complex) * state mode) 2 :=
    (lp.memℓp state).const_mul ((|holonomy - reference| : ℝ) : Complex)
  have hPerturbation : Memℓp perturbation 2 := hScaled.mono' (fun mode => by
    change ‖((productThroatDiracEigenvalueAt data fold holonomy mode -
        productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) * state mode‖ ≤
      ‖((|holonomy - reference| : ℝ) : Complex) * state mode‖
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right
      (productThroatDiracEigenvalueAt_lipschitz
        data fold reference holonomy mode) (norm_nonneg _))
  exact ⟨perturbation, hPerturbation⟩

@[simp]
theorem productThroatDiracHolonomyPerturbationImage_apply
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference holonomy : ℝ) (state : ProductThroatHeatHilbert data)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracHolonomyPerturbationImage
        data fold reference holonomy state mode =
      ((productThroatDiracEigenvalueAt data fold holonomy mode -
        productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) * state mode :=
  rfl

theorem productThroatDiracHolonomyPerturbationImage_norm_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference holonomy : ℝ) (state : ProductThroatHeatHilbert data) :
    ‖productThroatDiracHolonomyPerturbationImage
        data fold reference holonomy state‖ ≤ |holonomy - reference| * ‖state‖ := by
  calc
    ‖productThroatDiracHolonomyPerturbationImage
        data fold reference holonomy state‖ ≤
        ‖(((|holonomy - reference| : ℝ) : Complex) • state)‖ :=
      lp.norm_mono (by norm_num) (fun mode => by
        change ‖((productThroatDiracEigenvalueAt data fold holonomy mode -
            productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) *
            state mode‖ ≤
          ‖((|holonomy - reference| : ℝ) : Complex) * state mode‖
        calc
          _ = |productThroatDiracEigenvalueAt data fold holonomy mode -
              productThroatDiracEigenvalueAt data fold reference mode| * ‖state mode‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |holonomy - reference| * ‖state mode‖ :=
            mul_le_mul_of_nonneg_right
              (productThroatDiracEigenvalueAt_lipschitz
                data fold reference holonomy mode) (norm_nonneg _)
          _ = _ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs])
    _ = |holonomy - reference| * ‖state‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_abs]

def productThroatDiracHolonomyPerturbationOperator
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference holonomy : ℝ) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  LinearMap.mkContinuous
    { toFun := productThroatDiracHolonomyPerturbationImage
        data fold reference holonomy
      map_add' := by
        intro first second
        ext mode
        simp [productThroatDiracHolonomyPerturbationImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [productThroatDiracHolonomyPerturbationImage_apply]
        ring }
    |holonomy - reference| (fun state => by
      simpa using productThroatDiracHolonomyPerturbationImage_norm_le
        data fold reference holonomy state)

@[simp]
theorem productThroatDiracHolonomyPerturbationOperator_apply
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference holonomy : ℝ) (state : ProductThroatHeatHilbert data) :
    productThroatDiracHolonomyPerturbationOperator data fold reference holonomy state =
      productThroatDiracHolonomyPerturbationImage data fold reference holonomy state :=
  rfl

@[simp]
theorem productThroatDiracHolonomyDerivativeOperator_apply
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) :
    productThroatDiracHolonomyDerivativeOperator data fold holonomy state =
      productThroatDiracHolonomyDerivativeImage data fold holonomy state :=
  rfl

theorem productThroatDiracHolonomyPerturbationOperator_norm_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference holonomy : ℝ) :
    ‖productThroatDiracHolonomyPerturbationOperator
        data fold reference holonomy‖ ≤ |holonomy - reference| := by
  apply ContinuousLinearMap.opNorm_le_bound
    (productThroatDiracHolonomyPerturbationOperator data fold reference holonomy)
    (abs_nonneg _)
  intro state
  exact productThroatDiracHolonomyPerturbationImage_norm_le
    data fold reference holonomy state

theorem productThroatDiracEigenvalueAt_taylor_remainder_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : ℝ) (mode : ProductThroatHeatMode data) :
    |productThroatDiracEigenvalueAt data fold second mode -
        productThroatDiracEigenvalueAt data fold first mode -
        productThroatDiracHolonomyDerivativeCoefficient data fold first mode *
          (second - first)| ≤
      (productThroatDiracGap data)⁻¹ * |second - first| ^ 2 := by
  let adjusted : ℝ → ℝ := fun parameter =>
    productThroatDiracEigenvalueAt data fold parameter mode -
      productThroatDiracHolonomyDerivativeCoefficient data fold first mode * parameter
  have hDerivative : ∀ parameter : ℝ,
      HasDerivAt adjusted
        (productThroatDiracHolonomyDerivativeCoefficient data fold parameter mode -
          productThroatDiracHolonomyDerivativeCoefficient data fold first mode)
        parameter := by
    intro parameter
    have hRaw := (productThroatDiracEigenvalueAt_hasDerivAt
      data fold parameter mode).sub
      ((hasDerivAt_id parameter).const_mul
        (productThroatDiracHolonomyDerivativeCoefficient data fold first mode))
    have hRaw' : HasDerivAt
        ((fun x => productThroatDiracEigenvalueAt data fold x mode) -
          fun x => productThroatDiracHolonomyDerivativeCoefficient
            data fold first mode * x)
        (productThroatDiracHolonomyDerivativeCoefficient data fold parameter mode -
          productThroatDiracHolonomyDerivativeCoefficient data fold first mode)
        parameter := by
      simpa using hRaw
    apply hRaw'.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have hMVT := (convex_uIcc first second).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := adjusted)
    (f' := fun parameter =>
      productThroatDiracHolonomyDerivativeCoefficient data fold parameter mode -
        productThroatDiracHolonomyDerivativeCoefficient data fold first mode)
    (C := (productThroatDiracGap data)⁻¹ * |second - first|)
    (fun parameter _ => (hDerivative parameter).hasDerivWithinAt)
    (fun parameter hParameter => by
      rw [Real.norm_eq_abs]
      exact le_trans
        (productThroatDiracHolonomyDerivativeCoefficient_lipschitz
          data fold first parameter mode)
        (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hParameter)
          (inv_nonneg.mpr (productThroatDiracGap_positive data).le)))
    left_mem_uIcc right_mem_uIcc
  calc
    |productThroatDiracEigenvalueAt data fold second mode -
        productThroatDiracEigenvalueAt data fold first mode -
        productThroatDiracHolonomyDerivativeCoefficient data fold first mode *
          (second - first)| = ‖adjusted second - adjusted first‖ := by
      rw [Real.norm_eq_abs]
      congr 1
      simp only [adjusted]
      ring
    _ ≤ (productThroatDiracGap data)⁻¹ * |second - first| * ‖second - first‖ := hMVT
    _ = (productThroatDiracGap data)⁻¹ * |second - first| ^ 2 := by
      rw [Real.norm_eq_abs]
      ring

theorem productThroatDiracHolonomyPerturbationOperator_taylor_remainder_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference first second : ℝ) :
    ‖productThroatDiracHolonomyPerturbationOperator data fold reference second -
        productThroatDiracHolonomyPerturbationOperator data fold reference first -
        (second - first) •
          productThroatDiracHolonomyDerivativeOperator data fold first‖ ≤
      (productThroatDiracGap data)⁻¹ * |second - first| ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (inv_nonneg.mpr (productThroatDiracGap_positive data).le)
      (sq_nonneg _)
  · intro state
    calc
      ‖(productThroatDiracHolonomyPerturbationOperator data fold reference second -
          productThroatDiracHolonomyPerturbationOperator data fold reference first -
          (second - first) •
            productThroatDiracHolonomyDerivativeOperator data fold first) state‖ ≤
          ‖(((productThroatDiracGap data)⁻¹ * |second - first| ^ 2 : ℝ) : Complex) •
            state‖ := lp.norm_mono (by norm_num) (fun mode => by
              simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
                productThroatDiracHolonomyPerturbationOperator_apply,
                productThroatDiracHolonomyDerivativeOperator_apply]
              rw [show
                (productThroatDiracHolonomyPerturbationImage data fold reference second state -
                    productThroatDiracHolonomyPerturbationImage data fold reference first state -
                    (second - first) •
                      productThroatDiracHolonomyDerivativeImage data fold first state) mode =
                  ((productThroatDiracEigenvalueAt data fold second mode -
                  productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) *
                    state mode -
                ((productThroatDiracEigenvalueAt data fold first mode -
                  productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) *
                    state mode -
                ((second - first : ℝ) : Complex) *
                  ((productThroatDiracHolonomyDerivativeCoefficient
                    data fold first mode : ℝ) : Complex) * state mode by
                      simp [productThroatDiracHolonomyPerturbationImage_apply,
                        productThroatDiracHolonomyDerivativeImage_apply]
                      ring,
                show ((((productThroatDiracGap data)⁻¹ * |second - first| ^ 2 : ℝ) : Complex) •
                    state) mode =
                  (((productThroatDiracGap data)⁻¹ * |second - first| ^ 2 : ℝ) : Complex) *
                    state mode by rfl]
              rw [show
                ((productThroatDiracEigenvalueAt data fold second mode -
                    productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) *
                      state mode -
                  ((productThroatDiracEigenvalueAt data fold first mode -
                    productThroatDiracEigenvalueAt data fold reference mode : ℝ) : Complex) *
                      state mode -
                  ((second - first : ℝ) : Complex) *
                    ((productThroatDiracHolonomyDerivativeCoefficient
                      data fold first mode : ℝ) : Complex) * state mode =
                  ((productThroatDiracEigenvalueAt data fold second mode -
                    productThroatDiracEigenvalueAt data fold first mode -
                    productThroatDiracHolonomyDerivativeCoefficient data fold first mode *
                      (second - first) : ℝ) : Complex) * state mode by
                    push_cast
                    ring]
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (mul_nonneg
                  (inv_nonneg.mpr (productThroatDiracGap_positive data).le) (sq_nonneg _))]
              exact mul_le_mul_of_nonneg_right
                (productThroatDiracEigenvalueAt_taylor_remainder_le
                  data fold first second mode) (norm_nonneg _))
      _ = ((productThroatDiracGap data)⁻¹ * |second - first| ^ 2) * ‖state‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg
            (inv_nonneg.mpr (productThroatDiracGap_positive data).le) (sq_nonneg _))]

theorem productThroatDiracHolonomyPerturbation_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference holonomy : ℝ) :
    HasDerivAt
      (fun parameter => productThroatDiracHolonomyPerturbationOperator
        data fold reference parameter)
      (productThroatDiracHolonomyDerivativeOperator data fold holonomy)
      holonomy := by
  apply HasDerivAt.of_isLittleO
  have hBigO :
      (fun parameter =>
        productThroatDiracHolonomyPerturbationOperator data fold reference parameter -
          productThroatDiracHolonomyPerturbationOperator data fold reference holonomy -
          (parameter - holonomy) •
            productThroatDiracHolonomyDerivativeOperator data fold holonomy) =O[𝓝 holonomy]
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
    have hBound : IsBigOWith (productThroatDiracGap data)⁻¹ (𝓝 holonomy)
        (fun parameter =>
          productThroatDiracHolonomyPerturbationOperator data fold reference parameter -
            productThroatDiracHolonomyPerturbationOperator data fold reference holonomy -
            (parameter - holonomy) •
              productThroatDiracHolonomyDerivativeOperator data fold holonomy)
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
      apply IsBigOWith.of_bound
      filter_upwards with parameter
      simpa only [norm_pow, norm_norm, Real.norm_eq_abs, abs_abs] using
        (productThroatDiracHolonomyPerturbationOperator_taylor_remainder_le
          data fold reference holonomy parameter)
    exact hBound.isBigO
  exact hBigO.trans_isLittleO (isLittleO_pow_sub_sub holonomy (by norm_num : 1 < 2))

end

end P0EFTJanusProductThroatHolonomyOperatorDifferentiable4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomySecondDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphFamily4D

/-!
# Second derivative on the common graph domain

The bounded diagonal second derivative is transported through the fixed graph
projection.  The uniform operator Taylor estimate then proves norm
differentiability of the common-graph first derivative family.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphSecondDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open Asymptotics Filter
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open P0EFTJanusProductThroatHolonomySecondDerivative4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D
open scoped Topology

/-- Exact second derivative on the fixed common graph domain. -/
def productThroatCommonGraphDiracSecondDerivativeCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data :=
  (productThroatDiracHolonomySecondDerivativeOperator
    data fold holonomy).comp
      (productThroatCommonGraphFstCLM data fold reference)

def productThroatCommonGraphDiracSecondDerivativeReal
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) : ProductThroatCommonGraphOperatorReal data fold reference :=
  productThroatCommonGraphDiracSecondDerivativeCLM
    data fold reference holonomy

theorem productThroatCommonGraphDiracDerivative_taylor_remainder_le
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (first second : ℝ) :
    ‖productThroatCommonGraphDiracDerivativeReal data fold reference second -
        productThroatCommonGraphDiracDerivativeReal data fold reference first -
        (second - first) •
          productThroatCommonGraphDiracSecondDerivativeReal
            data fold reference first‖ ≤
      (3 * (productThroatDiracGap data ^ 2)⁻¹) * |second - first| ^ 2 := by
  unfold productThroatCommonGraphDiracDerivativeReal
    productThroatCommonGraphDiracSecondDerivativeReal
    ProductThroatCommonGraphOperatorReal
  change ‖productThroatCommonGraphDiracDerivativeCLM data fold reference second -
      productThroatCommonGraphDiracDerivativeCLM data fold reference first -
      (second - first) •
        productThroatCommonGraphDiracSecondDerivativeCLM
          data fold reference first‖ ≤ _
  calc
    _ = ‖(productThroatDiracHolonomyDerivativeOperator data fold second -
          productThroatDiracHolonomyDerivativeOperator data fold first -
          (second - first) •
            productThroatDiracHolonomySecondDerivativeOperator
              data fold first).comp
        (productThroatCommonGraphFstCLM data fold reference)‖ := by
      congr 1
    _ ≤ ‖productThroatDiracHolonomyDerivativeOperator data fold second -
          productThroatDiracHolonomyDerivativeOperator data fold first -
          (second - first) •
            productThroatDiracHolonomySecondDerivativeOperator
              data fold first‖ *
        ‖productThroatCommonGraphFstCLM data fold reference‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((3 * (productThroatDiracGap data ^ 2)⁻¹) *
          |second - first| ^ 2) * 1 :=
      mul_le_mul
        (productThroatDiracHolonomyDerivativeOperator_taylor_remainder_le
          data fold first second)
        (productThroatCommonGraphFstCLM_norm_le data fold reference)
        (norm_nonneg (productThroatCommonGraphFstCLM data fold reference))
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
          (sq_nonneg _))
    _ = _ := mul_one _

theorem productThroatCommonGraphDiracDerivative_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    HasDerivAt
      (productThroatCommonGraphDiracDerivativeReal data fold reference)
      (productThroatCommonGraphDiracSecondDerivativeReal
        data fold reference holonomy)
      holonomy := by
  apply HasDerivAt.of_isLittleO
  have hBigO :
      (fun parameter =>
        productThroatCommonGraphDiracDerivativeReal data fold reference parameter -
          productThroatCommonGraphDiracDerivativeReal data fold reference holonomy -
          (parameter - holonomy) •
            productThroatCommonGraphDiracSecondDerivativeReal
              data fold reference holonomy) =O[nhds holonomy]
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
    have hBound : IsBigOWith
        (3 * (productThroatDiracGap data ^ 2)⁻¹) (nhds holonomy)
        (fun parameter =>
          productThroatCommonGraphDiracDerivativeReal data fold reference parameter -
            productThroatCommonGraphDiracDerivativeReal data fold reference holonomy -
            (parameter - holonomy) •
              productThroatCommonGraphDiracSecondDerivativeReal
                data fold reference holonomy)
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
      apply IsBigOWith.of_bound
      filter_upwards with parameter
      simpa only [norm_pow, norm_norm, Real.norm_eq_abs, abs_abs] using
        (productThroatCommonGraphDiracDerivative_taylor_remainder_le
          data fold reference holonomy parameter)
    exact hBound.isBigO
  exact hBigO.trans_isLittleO
    (isLittleO_pow_sub_sub holonomy (by norm_num : 1 < 2))

theorem productThroatCommonGraphDiracSecondDerivative_sub_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (first second : ℝ) :
    ‖productThroatCommonGraphDiracSecondDerivativeCLM
          data fold reference second -
        productThroatCommonGraphDiracSecondDerivativeCLM
          data fold reference first‖ ≤
      (3 * (productThroatDiracGap data ^ 2)⁻¹) * |second - first| := by
  calc
    _ = ‖(productThroatDiracHolonomySecondDerivativeOperator data fold second -
          productThroatDiracHolonomySecondDerivativeOperator data fold first).comp
        (productThroatCommonGraphFstCLM data fold reference)‖ := by
      rfl
    _ ≤ ‖productThroatDiracHolonomySecondDerivativeOperator data fold second -
          productThroatDiracHolonomySecondDerivativeOperator data fold first‖ *
        ‖productThroatCommonGraphFstCLM data fold reference‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((3 * (productThroatDiracGap data ^ 2)⁻¹) *
          |second - first|) * 1 :=
      mul_le_mul
        (productThroatDiracHolonomySecondDerivativeOperator_sub_norm_le
          data fold first second)
        (productThroatCommonGraphFstCLM_norm_le data fold reference)
        (norm_nonneg (productThroatCommonGraphFstCLM data fold reference))
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data))))
          (abs_nonneg _))
    _ = _ := mul_one _

theorem productThroatCommonGraphDiracSecondDerivative_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    LipschitzWith
      ⟨3 * (productThroatDiracGap data ^ 2)⁻¹,
        mul_nonneg (by norm_num)
          (inv_nonneg.mpr (sq_nonneg (productThroatDiracGap data)))⟩
      (productThroatCommonGraphDiracSecondDerivativeReal
        data fold reference) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simp only [dist_eq_norm, Real.norm_eq_abs]
  unfold productThroatCommonGraphDiracSecondDerivativeReal
    ProductThroatCommonGraphOperatorReal
  change ‖productThroatCommonGraphDiracSecondDerivativeCLM
      data fold reference first -
      productThroatCommonGraphDiracSecondDerivativeCLM
        data fold reference second‖ ≤
    (3 * (productThroatDiracGap data ^ 2)⁻¹) * |first - second|
  simpa [abs_sub_comm] using
    (productThroatCommonGraphDiracSecondDerivative_sub_norm_le
      data fold reference second first)

theorem productThroatCommonGraphDiracDerivative_contDiff_one
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 1
      (productThroatCommonGraphDiracDerivativeReal data fold reference) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro holonomy
    exact (productThroatCommonGraphDiracDerivative_hasDerivAt
      data fold reference holonomy).differentiableAt
  · have hDeriv :
        deriv (productThroatCommonGraphDiracDerivativeReal data fold reference) =
          productThroatCommonGraphDiracSecondDerivativeReal
            data fold reference := by
      funext holonomy
      exact (productThroatCommonGraphDiracDerivative_hasDerivAt
        data fold reference holonomy).deriv
    exact hDeriv.symm ▸
      (productThroatCommonGraphDiracSecondDerivative_lipschitz
        data fold reference).continuous

theorem productThroatCommonGraphDirac_contDiff_two
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 2 (productThroatCommonGraphDiracReal data fold reference) := by
  change ContDiff ℝ (1 + 1)
    (productThroatCommonGraphDiracReal data fold reference)
  rw [contDiff_succ_iff_deriv]
  refine ⟨(productThroatCommonGraphDirac_contDiff_one
    data fold reference).differentiable (by norm_num), ?_, ?_⟩
  · intro hImpossible
    norm_num at hImpossible
  · have hDeriv :
        deriv (productThroatCommonGraphDiracReal data fold reference) =
          productThroatCommonGraphDiracDerivativeReal data fold reference := by
      funext holonomy
      exact (productThroatCommonGraphDirac_hasDerivAt
        data fold reference holonomy).deriv
    exact hDeriv.symm ▸
      productThroatCommonGraphDiracDerivative_contDiff_one
        data fold reference

/-- Exact third derivative on the fixed common graph domain. -/
def productThroatCommonGraphDiracThirdDerivativeCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data :=
  (productThroatDiracHolonomyThirdDerivativeOperator
    data fold holonomy).comp
      (productThroatCommonGraphFstCLM data fold reference)

def productThroatCommonGraphDiracThirdDerivativeReal
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) : ProductThroatCommonGraphOperatorReal data fold reference :=
  productThroatCommonGraphDiracThirdDerivativeCLM
    data fold reference holonomy

theorem productThroatCommonGraphDiracSecondDerivative_taylor_remainder_le
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (first second : ℝ) :
    ‖productThroatCommonGraphDiracSecondDerivativeReal
          data fold reference second -
        productThroatCommonGraphDiracSecondDerivativeReal
          data fold reference first -
        (second - first) •
          productThroatCommonGraphDiracThirdDerivativeReal
            data fold reference first‖ ≤
      (15 * (productThroatDiracGap data ^ 3)⁻¹) * |second - first| ^ 2 := by
  unfold productThroatCommonGraphDiracSecondDerivativeReal
    productThroatCommonGraphDiracThirdDerivativeReal
    ProductThroatCommonGraphOperatorReal
  change ‖productThroatCommonGraphDiracSecondDerivativeCLM
      data fold reference second -
      productThroatCommonGraphDiracSecondDerivativeCLM
        data fold reference first -
      (second - first) •
        productThroatCommonGraphDiracThirdDerivativeCLM
          data fold reference first‖ ≤ _
  calc
    _ = ‖(productThroatDiracHolonomySecondDerivativeOperator data fold second -
          productThroatDiracHolonomySecondDerivativeOperator data fold first -
          (second - first) •
            productThroatDiracHolonomyThirdDerivativeOperator
              data fold first).comp
        (productThroatCommonGraphFstCLM data fold reference)‖ := by
      congr 1
    _ ≤ ‖productThroatDiracHolonomySecondDerivativeOperator data fold second -
          productThroatDiracHolonomySecondDerivativeOperator data fold first -
          (second - first) •
            productThroatDiracHolonomyThirdDerivativeOperator
              data fold first‖ *
        ‖productThroatCommonGraphFstCLM data fold reference‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((15 * (productThroatDiracGap data ^ 3)⁻¹) *
          |second - first| ^ 2) * 1 :=
      mul_le_mul
        (productThroatDiracHolonomySecondDerivativeOperator_taylor_remainder_le
          data fold first second)
        (productThroatCommonGraphFstCLM_norm_le data fold reference)
        (norm_nonneg (productThroatCommonGraphFstCLM data fold reference))
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (inv_nonneg.mpr (pow_nonneg
              (productThroatDiracGap_positive data).le 3)))
          (sq_nonneg _))
    _ = _ := mul_one _

theorem productThroatCommonGraphDiracSecondDerivative_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    HasDerivAt
      (productThroatCommonGraphDiracSecondDerivativeReal data fold reference)
      (productThroatCommonGraphDiracThirdDerivativeReal
        data fold reference holonomy)
      holonomy := by
  apply HasDerivAt.of_isLittleO
  have hBigO :
      (fun parameter =>
        productThroatCommonGraphDiracSecondDerivativeReal
            data fold reference parameter -
          productThroatCommonGraphDiracSecondDerivativeReal
            data fold reference holonomy -
          (parameter - holonomy) •
            productThroatCommonGraphDiracThirdDerivativeReal
              data fold reference holonomy) =O[nhds holonomy]
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
    have hBound : IsBigOWith
        (15 * (productThroatDiracGap data ^ 3)⁻¹) (nhds holonomy)
        (fun parameter =>
          productThroatCommonGraphDiracSecondDerivativeReal
              data fold reference parameter -
            productThroatCommonGraphDiracSecondDerivativeReal
              data fold reference holonomy -
            (parameter - holonomy) •
              productThroatCommonGraphDiracThirdDerivativeReal
                data fold reference holonomy)
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
      apply IsBigOWith.of_bound
      filter_upwards with parameter
      simpa only [norm_pow, norm_norm, Real.norm_eq_abs, abs_abs] using
        (productThroatCommonGraphDiracSecondDerivative_taylor_remainder_le
          data fold reference holonomy parameter)
    exact hBound.isBigO
  exact hBigO.trans_isLittleO
    (isLittleO_pow_sub_sub holonomy (by norm_num : 1 < 2))

theorem productThroatCommonGraphDiracThirdDerivative_sub_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (first second : ℝ) :
    ‖productThroatCommonGraphDiracThirdDerivativeCLM
          data fold reference second -
        productThroatCommonGraphDiracThirdDerivativeCLM
          data fold reference first‖ ≤
      (15 * (productThroatDiracGap data ^ 3)⁻¹) * |second - first| := by
  calc
    _ = ‖(productThroatDiracHolonomyThirdDerivativeOperator data fold second -
          productThroatDiracHolonomyThirdDerivativeOperator data fold first).comp
        (productThroatCommonGraphFstCLM data fold reference)‖ := by rfl
    _ ≤ ‖productThroatDiracHolonomyThirdDerivativeOperator data fold second -
          productThroatDiracHolonomyThirdDerivativeOperator data fold first‖ *
        ‖productThroatCommonGraphFstCLM data fold reference‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((15 * (productThroatDiracGap data ^ 3)⁻¹) *
          |second - first|) * 1 :=
      mul_le_mul
        (productThroatDiracHolonomyThirdDerivativeOperator_sub_norm_le
          data fold first second)
        (productThroatCommonGraphFstCLM_norm_le data fold reference)
        (norm_nonneg (productThroatCommonGraphFstCLM data fold reference))
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (inv_nonneg.mpr (pow_nonneg
              (productThroatDiracGap_positive data).le 3)))
          (abs_nonneg _))
    _ = _ := mul_one _

theorem productThroatCommonGraphDiracThirdDerivative_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    LipschitzWith
      ⟨15 * (productThroatDiracGap data ^ 3)⁻¹,
        mul_nonneg (by norm_num)
          (inv_nonneg.mpr (pow_nonneg
            (productThroatDiracGap_positive data).le 3))⟩
      (productThroatCommonGraphDiracThirdDerivativeReal
        data fold reference) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simp only [dist_eq_norm, Real.norm_eq_abs]
  unfold productThroatCommonGraphDiracThirdDerivativeReal
    ProductThroatCommonGraphOperatorReal
  change ‖productThroatCommonGraphDiracThirdDerivativeCLM
      data fold reference first -
      productThroatCommonGraphDiracThirdDerivativeCLM
        data fold reference second‖ ≤
    (15 * (productThroatDiracGap data ^ 3)⁻¹) * |first - second|
  simpa [abs_sub_comm] using
    (productThroatCommonGraphDiracThirdDerivative_sub_norm_le
      data fold reference second first)

theorem productThroatCommonGraphDiracSecondDerivative_contDiff_one
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 1
      (productThroatCommonGraphDiracSecondDerivativeReal
        data fold reference) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro holonomy
    exact (productThroatCommonGraphDiracSecondDerivative_hasDerivAt
      data fold reference holonomy).differentiableAt
  · have hDeriv :
        deriv (productThroatCommonGraphDiracSecondDerivativeReal
          data fold reference) =
          productThroatCommonGraphDiracThirdDerivativeReal
            data fold reference := by
      funext holonomy
      exact (productThroatCommonGraphDiracSecondDerivative_hasDerivAt
        data fold reference holonomy).deriv
    exact hDeriv.symm ▸
      (productThroatCommonGraphDiracThirdDerivative_lipschitz
        data fold reference).continuous

theorem productThroatCommonGraphDiracDerivative_contDiff_two
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 2
      (productThroatCommonGraphDiracDerivativeReal data fold reference) := by
  change ContDiff ℝ (1 + 1)
    (productThroatCommonGraphDiracDerivativeReal data fold reference)
  rw [contDiff_succ_iff_deriv]
  refine ⟨(productThroatCommonGraphDiracDerivative_contDiff_one
    data fold reference).differentiable (by norm_num), ?_, ?_⟩
  · intro hImpossible
    norm_num at hImpossible
  · have hDeriv :
        deriv (productThroatCommonGraphDiracDerivativeReal data fold reference) =
          productThroatCommonGraphDiracSecondDerivativeReal
            data fold reference := by
      funext holonomy
      exact (productThroatCommonGraphDiracDerivative_hasDerivAt
        data fold reference holonomy).deriv
    exact hDeriv.symm ▸
      productThroatCommonGraphDiracSecondDerivative_contDiff_one
        data fold reference

theorem productThroatCommonGraphDirac_contDiff_three
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 3 (productThroatCommonGraphDiracReal data fold reference) := by
  change ContDiff ℝ (2 + 1)
    (productThroatCommonGraphDiracReal data fold reference)
  rw [contDiff_succ_iff_deriv]
  refine ⟨(productThroatCommonGraphDirac_contDiff_two
    data fold reference).differentiable (by norm_num), ?_, ?_⟩
  · intro hImpossible
    norm_num at hImpossible
  · have hDeriv :
        deriv (productThroatCommonGraphDiracReal data fold reference) =
          productThroatCommonGraphDiracDerivativeReal
            data fold reference := by
      funext holonomy
      exact (productThroatCommonGraphDirac_hasDerivAt
        data fold reference holonomy).deriv
    exact hDeriv.symm ▸
      productThroatCommonGraphDiracDerivative_contDiff_two
        data fold reference

end

end P0EFTJanusProductThroatHolonomyGraphSecondDerivative4D
end JanusFormal

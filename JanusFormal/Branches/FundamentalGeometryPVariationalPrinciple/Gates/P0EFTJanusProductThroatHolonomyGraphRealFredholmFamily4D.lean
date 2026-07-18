import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphFredholmFamily4D
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Real-holonomy invertibility of the common graph family

The sphere contribution gives a uniform gap for every real holonomy, not only
for parameters packaged as `CircleTwist`.  We construct the reciprocal
multiplier, place its image in the fixed reference domain, and obtain a
continuous linear equivalence for every real fiber.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphRealFredholmFamily4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open P0EFTJanusProductThroatHolonomyOperatorDifferentiable4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D
open P0EFTJanusProductThroatHolonomyGraphFredholmFamily4D
open scoped ENNReal lp

theorem productThroatDiracGap_le_abs_eigenvalueAt
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracGap data ≤
      |productThroatDiracEigenvalueAt data fold holonomy mode| := by
  rw [productThroatDiracEigenvalueAt, abs_mul]
  have hSign : |fold.spectralSign| = 1 := by cases fold <;> norm_num
  rw [hSign, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact le_trans (sphereEigenvalueSquared_zero_le data mode.1.1)
    (le_add_of_nonneg_right (sq_nonneg _))

theorem productThroatDiracEigenvalueAt_ne_zero
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracEigenvalueAt data fold holonomy mode ≠ 0 := by
  intro hZero
  have hGap := productThroatDiracGap_le_abs_eigenvalueAt
    data fold holonomy mode
  rw [hZero, abs_zero] at hGap
  exact (not_lt_of_ge hGap) (productThroatDiracGap_positive data)

def productThroatDiracRealInverseCoefficient
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) : Complex :=
  (productThroatDiracEigenvalueAt data fold holonomy mode : Complex)⁻¹

theorem productThroatDiracRealInverseCoefficient_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    ‖productThroatDiracRealInverseCoefficient data fold holonomy mode‖ ≤
      (productThroatDiracGap data)⁻¹ := by
  rw [productThroatDiracRealInverseCoefficient, norm_inv,
    Complex.norm_real, Real.norm_eq_abs]
  exact inv_anti₀ (productThroatDiracGap_positive data)
    (productThroatDiracGap_le_abs_eigenvalueAt data fold holonomy mode)

def productThroatDiracRealInverseImage
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) : ProductThroatHeatHilbert data := by
  let inverse : ProductThroatHeatMode data → Complex := fun mode =>
    productThroatDiracRealInverseCoefficient data fold holonomy mode * state mode
  have hBound : Memℓp
      (fun mode : ProductThroatHeatMode data =>
        ((productThroatDiracGap data)⁻¹ : Complex) * state mode) 2 :=
    (lp.memℓp state).const_mul ((productThroatDiracGap data)⁻¹ : Complex)
  have hInverse : Memℓp inverse 2 := hBound.mono' (fun mode => by
    rw [show inverse mode =
      productThroatDiracRealInverseCoefficient data fold holonomy mode * state mode by rfl]
    calc
      _ = ‖productThroatDiracRealInverseCoefficient data fold holonomy mode‖ *
          ‖state mode‖ := norm_mul _ _
      _ ≤ (productThroatDiracGap data)⁻¹ * ‖state mode‖ :=
        mul_le_mul_of_nonneg_right
          (productThroatDiracRealInverseCoefficient_norm_le data fold holonomy mode)
          (norm_nonneg _)
      _ = _ := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (productThroatDiracGap_positive data)])
  exact ⟨inverse, hInverse⟩

@[simp] theorem productThroatDiracRealInverseImage_apply
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) (mode : ProductThroatHeatMode data) :
    productThroatDiracRealInverseImage data fold holonomy state mode =
      productThroatDiracRealInverseCoefficient data fold holonomy mode * state mode :=
  rfl

theorem productThroatDiracRealInverseImage_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) :
    ‖productThroatDiracRealInverseImage data fold holonomy state‖ ≤
      (productThroatDiracGap data)⁻¹ * ‖state‖ := by
  calc
    _ ≤ ‖(((productThroatDiracGap data)⁻¹ : ℝ) : Complex) • state‖ :=
      lp.norm_mono (by norm_num) (fun mode => by
        change ‖productThroatDiracRealInverseCoefficient data fold holonomy mode *
            state mode‖ ≤
          ‖(((productThroatDiracGap data)⁻¹ : ℝ) : Complex) * state mode‖
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (productThroatDiracGap_positive data).le)]
        exact mul_le_mul_of_nonneg_right
          (productThroatDiracRealInverseCoefficient_norm_le data fold holonomy mode)
          (norm_nonneg _))
    _ = _ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (productThroatDiracGap_positive data).le)]

theorem productThroatCommonGraph_reference_relation
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference)
    (mode : ProductThroatHeatMode data) :
    state.1.2 mode =
      (productThroatDiracEigenvalueAt data fold reference.value mode : Complex) *
        state.1.1 mode := by
  let domainState := productThroatCommonGraphDomainState data fold reference state
  have hImage : state.1.2 =
      productThroatUnboundedDirac data fold reference domainState := by
    exact (productThroatUnboundedDirac data fold reference).mem_graph_snd_inj'
      state.property
      ((productThroatUnboundedDirac data fold reference).mem_graph domainState) rfl
  rw [hImage, productThroatUnboundedDirac_apply,
    productThroatDiracEigenvalueAt_twist]
  rfl

theorem productThroatCommonGraphDirac_apply_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) (state : ProductThroatCommonGraphDomain data fold reference)
    (mode : ProductThroatHeatMode data) :
    productThroatCommonGraphDiracCLM data fold reference holonomy state mode =
      (productThroatDiracEigenvalueAt data fold holonomy mode : Complex) *
        state.1.1 mode := by
  rw [productThroatCommonGraphDiracCLM_apply]
  change state.1.2 mode +
      ((productThroatDiracEigenvalueAt data fold holonomy mode -
        productThroatDiracEigenvalueAt data fold reference.value mode : ℝ) : Complex) *
          state.1.1 mode = _
  rw [productThroatCommonGraph_reference_relation]
  push_cast
  ring

theorem productThroatDiracRealInverseImage_mem_referenceDomain
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) (state : ProductThroatHeatHilbert data) :
    productThroatDiracRealInverseImage data fold holonomy state ∈
      productThroatDiracDomain data fold reference := by
  let inverse := productThroatDiracRealInverseImage data fold holonomy state
  let image := state - productThroatDiracHolonomyPerturbationOperator
    data fold reference.value holonomy inverse
  refine ⟨image, fun mode => ?_⟩
  change state mode -
      ((productThroatDiracEigenvalueAt data fold holonomy mode -
        productThroatDiracEigenvalueAt data fold reference.value mode : ℝ) : Complex) *
          inverse mode =
    (productThroatDiracEigenvalue data fold reference mode : Complex) * inverse mode
  rw [show inverse mode =
      productThroatDiracRealInverseCoefficient data fold holonomy mode * state mode by rfl,
    productThroatDiracRealInverseCoefficient,
    ← productThroatDiracEigenvalueAt_twist data fold reference mode]
  have hEigen : (productThroatDiracEigenvalueAt data fold holonomy mode : Complex) ≠ 0 := by
    exact_mod_cast productThroatDiracEigenvalueAt_ne_zero data fold holonomy mode
  push_cast
  field_simp [hEigen]
  ring

def productThroatCommonGraphRealInverse
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) (state : ProductThroatHeatHilbert data) :
    ProductThroatCommonGraphDomain data fold reference :=
  productThroatCommonGraphStateOfDomain data fold reference
    ⟨productThroatDiracRealInverseImage data fold holonomy state,
      productThroatDiracRealInverseImage_mem_referenceDomain
        data fold reference holonomy state⟩

theorem productThroatCommonGraphDirac_rightInverse_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) (state : ProductThroatHeatHilbert data) :
    productThroatCommonGraphDiracCLM data fold reference holonomy
      (productThroatCommonGraphRealInverse data fold reference holonomy state) = state := by
  ext mode
  rw [productThroatCommonGraphDirac_apply_real]
  change (productThroatDiracEigenvalueAt data fold holonomy mode : Complex) *
      (productThroatDiracRealInverseCoefficient data fold holonomy mode * state mode) =
    state mode
  rw [productThroatDiracRealInverseCoefficient]
  have hEigen : (productThroatDiracEigenvalueAt data fold holonomy mode : Complex) ≠ 0 := by
    exact_mod_cast productThroatDiracEigenvalueAt_ne_zero data fold holonomy mode
  field_simp

theorem productThroatCommonGraphDirac_injective_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    Function.Injective (productThroatCommonGraphDiracCLM
      data fold reference holonomy) := by
  intro first second hEqual
  have hFst : first.1.1 = second.1.1 := by
    ext mode
    have hAt := congrArg
      (fun state : ProductThroatHeatHilbert data => state mode) hEqual
    rw [productThroatCommonGraphDirac_apply_real,
      productThroatCommonGraphDirac_apply_real] at hAt
    have hEigen : (productThroatDiracEigenvalueAt data fold holonomy mode : Complex) ≠ 0 := by
      exact_mod_cast productThroatDiracEigenvalueAt_ne_zero data fold holonomy mode
    exact mul_left_cancel₀ hEigen hAt
  have hDomain : productThroatCommonGraphDomainState data fold reference first =
      productThroatCommonGraphDomainState data fold reference second := by
    apply Subtype.ext
    exact hFst
  calc
    first = productThroatCommonGraphStateOfDomain data fold reference
        (productThroatCommonGraphDomainState data fold reference first) :=
      (productThroatCommonGraphStateOfDomain_domainState
        data fold reference first).symm
    _ = productThroatCommonGraphStateOfDomain data fold reference
        (productThroatCommonGraphDomainState data fold reference second) :=
      congrArg (productThroatCommonGraphStateOfDomain data fold reference) hDomain
    _ = second := productThroatCommonGraphStateOfDomain_domainState
      data fold reference second

theorem productThroatCommonGraphDirac_surjective_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    Function.Surjective (productThroatCommonGraphDiracCLM
      data fold reference holonomy) := fun state =>
  ⟨productThroatCommonGraphRealInverse data fold reference holonomy state,
    productThroatCommonGraphDirac_rightInverse_real
      data fold reference holonomy state⟩

theorem productThroatCommonGraphDirac_leftInverse_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphRealInverse data fold reference holonomy
      (productThroatCommonGraphDiracCLM data fold reference holonomy state) = state := by
  apply productThroatCommonGraphDirac_injective_real data fold reference holonomy
  rw [productThroatCommonGraphDirac_rightInverse_real]

/-- Every real-holonomy fiber is a bounded isomorphism from the common graph domain. -/
noncomputable def productThroatCommonGraphDiracContinuousLinearEquiv_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphDomain data fold reference ≃L[Complex]
      ProductThroatHeatHilbert data :=
  ContinuousLinearEquiv.ofBijective
    (productThroatCommonGraphDiracCLM data fold reference holonomy)
    (LinearMap.ker_eq_bot.mpr
      (productThroatCommonGraphDirac_injective_real data fold reference holonomy))
    (LinearMap.range_eq_top.mpr
      (productThroatCommonGraphDirac_surjective_real data fold reference holonomy))

theorem productThroatCommonGraphDiracIndex_real_zero
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    (productThroatCommonGraphDiracCLM
      data fold reference holonomy).toLinearMap.index = 0 := by
  rw [LinearMap.index_of_surjective
      (productThroatCommonGraphDirac_surjective_real data fold reference holonomy),
    LinearMap.ker_eq_bot.mpr
      (productThroatCommonGraphDirac_injective_real data fold reference holonomy)]
  simp

end

end P0EFTJanusProductThroatHolonomyGraphRealFredholmFamily4D
end JanusFormal

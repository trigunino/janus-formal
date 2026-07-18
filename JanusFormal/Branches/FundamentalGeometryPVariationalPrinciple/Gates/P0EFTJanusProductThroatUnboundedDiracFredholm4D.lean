import Mathlib.Algebra.Module.LinearMap.Index
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatUnboundedDirac4D

/-!
# Fredholm realization of the product-throat spectral Dirac operator

The strictly positive lowest sphere level gives a uniform spectral gap for
the first-order product Dirac operator.  Its reciprocal multiplier is bounded,
defines an inverse on the full spectral Hilbert space, and proves that the
maximal unbounded realization is bijective.  Consequently its kernel is zero,
its range is the full closed space, its algebraic cokernel is zero and its
Fredholm index is zero.

This is the separated product-throat operator, not the global geometric Janus
Dirac family.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatUnboundedDiracFredholm4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open P0EFTJanusProductThroatUnboundedDirac4D
open scoped ENNReal lp LinearPMap

/-- Positive bottom of the first-order product spectrum. -/
def productThroatDiracGap (data : ProductThroatSpectralData) : Real :=
  Real.sqrt (sphereEigenvalueSquared data 0)

theorem productThroatDiracGap_positive (data : ProductThroatSpectralData) :
    0 < productThroatDiracGap data := by
  exact Real.sqrt_pos.2 (sphere_eigenvalue_squared_positive data 0)

theorem sphereEigenvalueSquared_zero_le
    (data : ProductThroatSpectralData) (level : ℕ) :
    sphereEigenvalueSquared data 0 ≤ sphereEigenvalueSquared data level := by
  unfold sphereEigenvalueSquared
  have hRadius : 0 < data.sphereRadius ^ 2 :=
    sq_pos_of_pos data.sphereRadiusPositive
  apply (div_le_div_iff_of_pos_right hRadius).2
  norm_num
  have hLevel : 0 ≤ (level : Real) := by positivity
  have hCharge : 0 ≤ (monopoleAbsCharge data : Real) := by positivity
  nlinarith [mul_nonneg hLevel hLevel, mul_nonneg hLevel hCharge]

theorem productThroatDiracGap_le_abs_eigenvalue
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracGap data ≤
      |productThroatDiracEigenvalue data fold twist mode| := by
  rw [productThroatDiracEigenvalue, abs_mul]
  have hSign : |fold.spectralSign| = 1 := by cases fold <;> norm_num
  rw [hSign, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact le_trans (sphereEigenvalueSquared_zero_le data mode.1.1)
    (le_add_of_nonneg_right (by
      rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
      exact eigenvalueSq_nonnegative fold twist mode.2))

/-- Reciprocal spectral coefficient. -/
def productThroatDiracInverseCoefficient
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Complex :=
  (productThroatDiracEigenvalue data fold twist mode : Complex)⁻¹

theorem productThroatDiracEigenvalue_ne_zero
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracEigenvalue data fold twist mode ≠ 0 := by
  intro hZero
  have hGap := productThroatDiracGap_le_abs_eigenvalue data fold twist mode
  rw [hZero, abs_zero] at hGap
  exact (not_lt_of_ge hGap) (productThroatDiracGap_positive data)

theorem productThroatDiracInverseCoefficient_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ‖productThroatDiracInverseCoefficient data fold twist mode‖ ≤
      (productThroatDiracGap data)⁻¹ := by
  rw [productThroatDiracInverseCoefficient, norm_inv, Complex.norm_real,
    Real.norm_eq_abs]
  exact inv_anti₀ (productThroatDiracGap_positive data)
    (productThroatDiracGap_le_abs_eigenvalue data fold twist mode)

/-- The bounded reciprocal multiplier on the full product Hilbert space. -/
def productThroatDiracInverseImage
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : ProductThroatHeatHilbert data) : ProductThroatHeatHilbert data := by
  let inverse : ProductThroatHeatMode data → Complex := fun mode =>
    productThroatDiracInverseCoefficient data fold twist mode * state mode
  have hBound : Memℓp
      (fun mode : ProductThroatHeatMode data =>
        ((productThroatDiracGap data)⁻¹ : Complex) * state mode) 2 :=
    (lp.memℓp state).const_mul ((productThroatDiracGap data)⁻¹ : Complex)
  have hInverse : Memℓp inverse 2 := hBound.mono' (fun mode => by
    rw [show inverse mode =
      productThroatDiracInverseCoefficient data fold twist mode * state mode by rfl,
      norm_mul, norm_mul]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (productThroatDiracGap_positive data).le]
    exact mul_le_mul_of_nonneg_right
      (productThroatDiracInverseCoefficient_norm_le data fold twist mode)
      (norm_nonneg _))
  exact ⟨inverse, hInverse⟩

@[simp]
theorem productThroatDiracInverseImage_apply
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : ProductThroatHeatHilbert data)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracInverseImage data fold twist state mode =
      productThroatDiracInverseCoefficient data fold twist mode * state mode :=
  rfl

theorem productThroatDiracInverseImage_mem_domain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : ProductThroatHeatHilbert data) :
    productThroatDiracInverseImage data fold twist state ∈
      productThroatDiracDomain data fold twist := by
  refine ⟨state, fun mode => ?_⟩
  rw [productThroatDiracInverseImage_apply,
    productThroatDiracInverseCoefficient]
  have hEigen :
      (productThroatDiracEigenvalue data fold twist mode : Complex) ≠ 0 := by
    exact_mod_cast productThroatDiracEigenvalue_ne_zero data fold twist mode
  field_simp

/-- Inverse taking values in the maximal domain. -/
def productThroatDiracInverse
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : ProductThroatHeatHilbert data) :
    (productThroatUnboundedDirac data fold twist).domain :=
  ⟨productThroatDiracInverseImage data fold twist state,
    productThroatDiracInverseImage_mem_domain data fold twist state⟩

theorem productThroatUnboundedDirac_rightInverse
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : ProductThroatHeatHilbert data) :
    productThroatUnboundedDirac data fold twist
      (productThroatDiracInverse data fold twist state) = state := by
  ext mode
  rw [productThroatUnboundedDirac_apply]
  change (productThroatDiracEigenvalue data fold twist mode : Complex) *
    productThroatDiracInverseImage data fold twist state mode = state mode
  rw [
    productThroatDiracInverseImage_apply,
    productThroatDiracInverseCoefficient]
  have hEigen :
      (productThroatDiracEigenvalue data fold twist mode : Complex) ≠ 0 := by
    exact_mod_cast productThroatDiracEigenvalue_ne_zero data fold twist mode
  field_simp

theorem productThroatUnboundedDirac_leftInverse
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : (productThroatUnboundedDirac data fold twist).domain) :
    productThroatDiracInverse data fold twist
      (productThroatUnboundedDirac data fold twist state) = state := by
  apply Subtype.ext
  ext mode
  change productThroatDiracInverseImage data fold twist
    (productThroatUnboundedDirac data fold twist state) mode = state.1 mode
  rw [productThroatDiracInverseImage_apply,
    productThroatUnboundedDirac_apply,
    productThroatDiracInverseCoefficient]
  have hEigen :
      (productThroatDiracEigenvalue data fold twist mode : Complex) ≠ 0 := by
    exact_mod_cast productThroatDiracEigenvalue_ne_zero data fold twist mode
  field_simp

theorem productThroatUnboundedDirac_injective
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Function.Injective (productThroatUnboundedDirac data fold twist) := by
  intro first second hEqual
  rw [← productThroatUnboundedDirac_leftInverse data fold twist first,
    ← productThroatUnboundedDirac_leftInverse data fold twist second, hEqual]

theorem productThroatUnboundedDirac_surjective
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Function.Surjective (productThroatUnboundedDirac data fold twist) :=
  fun state => ⟨productThroatDiracInverse data fold twist state,
    productThroatUnboundedDirac_rightInverse data fold twist state⟩

theorem productThroatUnboundedDirac_ker_eq_bot
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    LinearMap.ker (productThroatUnboundedDirac data fold twist).toFun = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (productThroatUnboundedDirac_injective data fold twist)

theorem productThroatUnboundedDirac_range_eq_top
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    LinearMap.range (productThroatUnboundedDirac data fold twist).toFun = ⊤ :=
  LinearMap.range_eq_top.mpr
    (productThroatUnboundedDirac_surjective data fold twist)

theorem productThroatUnboundedDirac_range_isClosed
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    IsClosed
      (LinearMap.range (productThroatUnboundedDirac data fold twist).toFun :
        Set (ProductThroatHeatHilbert data)) := by
  rw [productThroatUnboundedDirac_range_eq_top data fold twist]
  exact isClosed_univ

/-- Algebraic cokernel of the maximal product Dirac realization. -/
abbrev ProductThroatDiracCokernel
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :=
  ProductThroatHeatHilbert data ⧸
    LinearMap.range (productThroatUnboundedDirac data fold twist).toFun

/-- Closed range and finite-dimensional kernel/cokernel. -/
theorem productThroatUnboundedDirac_fredholm_criterion
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    IsClosed
        (LinearMap.range (productThroatUnboundedDirac data fold twist).toFun :
          Set (ProductThroatHeatHilbert data)) ∧
      FiniteDimensional Complex
        (LinearMap.ker (productThroatUnboundedDirac data fold twist).toFun) ∧
      FiniteDimensional Complex (ProductThroatDiracCokernel data fold twist) := by
  refine ⟨productThroatUnboundedDirac_range_isClosed data fold twist, ?_, ?_⟩
  · rw [productThroatUnboundedDirac_ker_eq_bot data fold twist]
    infer_instance
  · change FiniteDimensional Complex
      (ProductThroatHeatHilbert data ⧸
        LinearMap.range (productThroatUnboundedDirac data fold twist).toFun)
    rw [productThroatUnboundedDirac_range_eq_top data fold twist]
    infer_instance

def productThroatUnboundedDiracIndex
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) : Int :=
  (productThroatUnboundedDirac data fold twist).toFun.index

theorem productThroatUnboundedDiracIndex_zero
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    productThroatUnboundedDiracIndex data fold twist = 0 := by
  unfold productThroatUnboundedDiracIndex
  rw [LinearMap.index_of_surjective
      (productThroatUnboundedDirac_surjective data fold twist),
    productThroatUnboundedDirac_ker_eq_bot data fold twist]
  simp

end

end P0EFTJanusProductThroatUnboundedDiracFredholm4D
end JanusFormal

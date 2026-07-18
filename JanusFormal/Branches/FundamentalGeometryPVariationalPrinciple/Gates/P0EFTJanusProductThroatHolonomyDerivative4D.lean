import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyCommonDomain4D

/-!
# Holonomy derivative of the product-throat spectral Dirac family

The circle holonomy is extended from its fundamental interval to a real
parameter.  Every product eigenvalue is smooth because the sphere contribution
is strictly positive.  Its derivative is computed explicitly, has absolute
value at most one, and therefore defines a bounded diagonal operator on the
full product Hilbert space.

This is a spectral fixed-geometry family, not yet the global Janus Fredholm
family over the physical parameter space.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyDerivative4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatHolonomyCommonDomain4D
open scoped ENNReal lp

/-- Positive squared product eigenvalue at an unrestricted real holonomy. -/
def productThroatDiracSquaredEigenvalueAt
    (data : ProductThroatSpectralData) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) : ℝ :=
  sphereEigenvalueSquared data mode.1.1 + ((mode.2 : ℝ) + holonomy) ^ 2

theorem productThroatDiracSquaredEigenvalueAt_positive
    (data : ProductThroatSpectralData) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    0 < productThroatDiracSquaredEigenvalueAt data holonomy mode := by
  exact add_pos_of_pos_of_nonneg
    (sphere_eigenvalue_squared_positive data mode.1.1) (sq_nonneg _)

/-- Signed first-order eigenvalue at unrestricted real holonomy. -/
def productThroatDiracEigenvalueAt
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) : ℝ :=
  fold.spectralSign *
    Real.sqrt (productThroatDiracSquaredEigenvalueAt data holonomy mode)

@[simp]
theorem productThroatDiracEigenvalueAt_twist
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracEigenvalueAt data fold twist.value mode =
      productThroatDiracEigenvalue data fold twist mode := by
  rw [productThroatDiracEigenvalueAt, productThroatDiracEigenvalue,
    productThroatDiracSquaredEigenvalue_eq_base]
  rfl

/-- Exact derivative coefficient of the real-holonomy eigenvalue. -/
def productThroatDiracHolonomyDerivativeCoefficient
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) : ℝ :=
  fold.spectralSign * ((mode.2 : ℝ) + holonomy) /
    Real.sqrt (productThroatDiracSquaredEigenvalueAt data holonomy mode)

theorem productThroatDiracEigenvalueAt_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    HasDerivAt
      (fun parameter => productThroatDiracEigenvalueAt data fold parameter mode)
      (productThroatDiracHolonomyDerivativeCoefficient
        data fold holonomy mode) holonomy := by
  let squared : ℝ → ℝ := fun parameter =>
    sphereEigenvalueSquared data mode.1.1 +
      ((mode.2 : ℝ) + parameter) ^ 2
  have hShifted : HasDerivAt
      (fun parameter : ℝ => (mode.2 : ℝ) + parameter) 1 holonomy := by
    rw [show (fun parameter : ℝ => (mode.2 : ℝ) + parameter) =
      fun parameter : ℝ => parameter + (mode.2 : ℝ) by
        funext parameter
        exact add_comm _ _]
    rw [hasDerivAt_add_const_iff]
    exact hasDerivAt_id holonomy
  have hSquared : HasDerivAt squared
      (2 * ((mode.2 : ℝ) + holonomy)) holonomy := by
    let raw : ℝ → ℝ :=
      (fun _ => sphereEigenvalueSquared data mode.1.1) +
        (fun parameter => (mode.2 : ℝ) + parameter) ^ 2
    have hRawBase := (hasDerivAt_const holonomy
      (sphereEigenvalueSquared data mode.1.1)).add (hShifted.pow 2)
    have hRaw : HasDerivAt raw
        (2 * ((mode.2 : ℝ) + holonomy)) holonomy := by
      apply hRawBase.congr_deriv
      norm_num
    apply hRaw.congr_of_eventuallyEq
    filter_upwards with parameter
    rfl
  have hPositive : 0 < squared holonomy := by
    exact add_pos_of_pos_of_nonneg
      (sphere_eigenvalue_squared_positive data mode.1.1) (sq_nonneg _)
  have hSqrt := hSquared.sqrt (ne_of_gt hPositive)
  have hScaled := hSqrt.const_mul fold.spectralSign
  have hDerivative :
      fold.spectralSign *
          (2 * ((mode.2 : ℝ) + holonomy) / (2 * Real.sqrt (squared holonomy))) =
        productThroatDiracHolonomyDerivativeCoefficient
          data fold holonomy mode := by
    unfold productThroatDiracHolonomyDerivativeCoefficient
    dsimp only [squared, productThroatDiracSquaredEigenvalueAt]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hPositive)]
  have hScaled' := hScaled.congr_deriv hDerivative
  simpa only [productThroatDiracEigenvalueAt,
    productThroatDiracSquaredEigenvalueAt, squared] using hScaled'

theorem productThroatDiracEigenvalueAt_contDiff
    (data : ProductThroatSpectralData) (fold : Fold)
    (mode : ProductThroatHeatMode data) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun holonomy => productThroatDiracEigenvalueAt data fold holonomy mode) := by
  have hSquared : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun holonomy : ℝ => sphereEigenvalueSquared data mode.1.1 +
        ((mode.2 : ℝ) + holonomy) ^ 2) := by fun_prop
  have hSqrt := hSquared.sqrt (fun holonomy => ne_of_gt
    (add_pos_of_pos_of_nonneg
      (sphere_eigenvalue_squared_positive data mode.1.1) (sq_nonneg _)))
  simpa [productThroatDiracEigenvalueAt,
    productThroatDiracSquaredEigenvalueAt] using
      (contDiff_const.mul hSqrt : ContDiff ℝ (⊤ : WithTop ℕ∞)
        (fun holonomy => fold.spectralSign *
          Real.sqrt (sphereEigenvalueSquared data mode.1.1 +
            ((mode.2 : ℝ) + holonomy) ^ 2)))

theorem productThroatDiracHolonomyDerivativeCoefficient_abs_le_one
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (mode : ProductThroatHeatMode data) :
    |productThroatDiracHolonomyDerivativeCoefficient data fold holonomy mode| ≤ 1 := by
  let shifted := (mode.2 : ℝ) + holonomy
  let energy := productThroatDiracSquaredEigenvalueAt data holonomy mode
  have hEnergy : 0 < energy :=
    productThroatDiracSquaredEigenvalueAt_positive data holonomy mode
  have hShiftedSq : shifted ^ 2 ≤ energy := by
    dsimp [energy, shifted, productThroatDiracSquaredEigenvalueAt]
    exact le_add_of_nonneg_left
      (sphere_eigenvalue_squared_positive data mode.1.1).le
  have hShifted : |shifted| ≤ Real.sqrt energy := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hShiftedSq
  rw [productThroatDiracHolonomyDerivativeCoefficient, abs_div, abs_mul]
  have hSign : |fold.spectralSign| = 1 := by cases fold <;> norm_num
  rw [hSign, one_mul, abs_of_nonneg (Real.sqrt_nonneg energy)]
  exact (div_le_one (Real.sqrt_pos.2 hEnergy)).2 hShifted

/-- The bounded diagonal derivative multiplier on the product Hilbert space. -/
def productThroatDiracHolonomyDerivativeImage
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) : ProductThroatHeatHilbert data := by
  let derivative : ProductThroatHeatMode data → Complex := fun mode =>
    (productThroatDiracHolonomyDerivativeCoefficient
      data fold holonomy mode : Complex) * state mode
  have hDerivative : Memℓp derivative 2 := (lp.memℓp state).mono' (fun mode => by
    rw [show derivative mode =
      (productThroatDiracHolonomyDerivativeCoefficient
        data fold holonomy mode : Complex) * state mode by rfl,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (productThroatDiracHolonomyDerivativeCoefficient_abs_le_one
        data fold holonomy mode)))
  exact ⟨derivative, hDerivative⟩

@[simp]
theorem productThroatDiracHolonomyDerivativeImage_apply
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracHolonomyDerivativeImage data fold holonomy state mode =
      (productThroatDiracHolonomyDerivativeCoefficient
        data fold holonomy mode : Complex) * state mode :=
  rfl

theorem productThroatDiracHolonomyDerivativeImage_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ)
    (state : ProductThroatHeatHilbert data) :
    ‖productThroatDiracHolonomyDerivativeImage data fold holonomy state‖ ≤
      ‖state‖ := by
  exact lp.norm_mono (by norm_num) (fun mode => by
    rw [productThroatDiracHolonomyDerivativeImage_apply, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (productThroatDiracHolonomyDerivativeCoefficient_abs_le_one
        data fold holonomy mode))

/-- Bounded derivative operator, of norm at most one. -/
def productThroatDiracHolonomyDerivativeOperator
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  LinearMap.mkContinuous
    { toFun := productThroatDiracHolonomyDerivativeImage data fold holonomy
      map_add' := by
        intro first second
        ext mode
        simp [productThroatDiracHolonomyDerivativeImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [productThroatDiracHolonomyDerivativeImage_apply]
        ring }
    1 (fun state => by
      simpa using productThroatDiracHolonomyDerivativeImage_norm_le
        data fold holonomy state)

theorem productThroatDiracHolonomyDerivativeOperator_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (holonomy : ℝ) :
    ‖productThroatDiracHolonomyDerivativeOperator data fold holonomy‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le
  norm_num

end

end P0EFTJanusProductThroatHolonomyDerivative4D
end JanusFormal

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
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
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

/-- Relative change of the squared eigenvalue around a real holonomy.  This is
the scalar input for a mode-uniform binomial functional calculus. -/
def productThroatDiracRelativeSquaredIncrement
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (mode : ProductThroatHeatMode data) : ℝ :=
  (productThroatDiracSquaredEigenvalueAt data (center + increment) mode -
      productThroatDiracSquaredEigenvalueAt data center mode) /
    productThroatDiracSquaredEigenvalueAt data center mode

/-- Exact multiplicative factorization by the relative squared increment. -/
theorem productThroatDiracSquaredEigenvalueAt_add_factorization
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracSquaredEigenvalueAt data (center + increment) mode =
      productThroatDiracSquaredEigenvalueAt data center mode *
        (1 + productThroatDiracRelativeSquaredIncrement
          data center increment mode) := by
  have hEnergy : productThroatDiracSquaredEigenvalueAt data center mode ≠ 0 :=
    ne_of_gt (productThroatDiracSquaredEigenvalueAt_positive data center mode)
  unfold productThroatDiracRelativeSquaredIncrement
  field_simp
  ring

/-- Uniform estimate for the relative squared increment.  Its constants depend
only on the positive product gap, never on the infinite mode label. -/
theorem productThroatDiracRelativeSquaredIncrement_abs_le
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (mode : ProductThroatHeatMode data) :
    |productThroatDiracRelativeSquaredIncrement data center increment mode| ≤
      2 * |increment| / productThroatDiracGap data +
        |increment| ^ 2 / productThroatDiracGap data ^ 2 := by
  let x : ℝ := (mode.2 : ℝ) + center
  let energy := productThroatDiracSquaredEigenvalueAt data center mode
  let gap := productThroatDiracGap data
  have hEnergy : 0 < energy :=
    productThroatDiracSquaredEigenvalueAt_positive data center mode
  have hGap : 0 < gap := productThroatDiracGap_positive data
  have hGapSq : gap ^ 2 ≤ energy := by
    dsimp [gap, energy, productThroatDiracGap,
      productThroatDiracSquaredEigenvalueAt]
    rw [Real.sq_sqrt
      (sphere_eigenvalue_squared_positive data 0).le]
    exact le_trans (sphereEigenvalueSquared_zero_le data mode.1.1)
      (le_add_of_nonneg_right (sq_nonneg _))
  have hXSq : x ^ 2 ≤ energy := by
    dsimp [x, energy, productThroatDiracSquaredEigenvalueAt]
    exact le_add_of_nonneg_left
      (sphere_eigenvalue_squared_positive data mode.1.1).le
  have hX : |x| ≤ Real.sqrt energy := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hXSq
  have hGapRoot : gap ≤ Real.sqrt energy := by
    have hRootNonnegative := Real.sqrt_nonneg energy
    have hRootSq := Real.sq_sqrt hEnergy.le
    nlinarith
  have hExpansion :
      productThroatDiracSquaredEigenvalueAt data (center + increment) mode -
          productThroatDiracSquaredEigenvalueAt data center mode =
        2 * x * increment + increment ^ 2 := by
    dsimp [x, productThroatDiracSquaredEigenvalueAt]
    ring
  have hNumerator : |2 * x * increment + increment ^ 2| ≤
      2 * |x| * |increment| + |increment| ^ 2 := by
    calc
      _ ≤ |2 * x * increment| + |increment ^ 2| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_pow]; norm_num
  have hXGap : |x| * gap ≤ energy := by
    calc
      |x| * gap ≤ Real.sqrt energy * Real.sqrt energy :=
        mul_le_mul hX hGapRoot hGap.le (Real.sqrt_nonneg energy)
      _ = energy := by rw [← pow_two, Real.sq_sqrt hEnergy.le]
  have hFirst : 2 * |x| * |increment| / energy ≤
      2 * |increment| / gap := by
    rw [div_le_div_iff₀ hEnergy hGap]
    nlinarith [mul_nonneg (abs_nonneg increment)
      (sub_nonneg.mpr hXGap)]
  have hSecond : |increment| ^ 2 / energy ≤
      |increment| ^ 2 / gap ^ 2 := by
    exact div_le_div_of_nonneg_left (sq_nonneg |increment|)
      (sq_pos_of_pos hGap) hGapSq
  unfold productThroatDiracRelativeSquaredIncrement
  rw [hExpansion, abs_div, abs_of_pos hEnergy]
  calc
    _ ≤ (2 * |x| * |increment| + |increment| ^ 2) / energy :=
      (div_le_div_iff_of_pos_right hEnergy).2 hNumerator
    _ = 2 * |x| * |increment| / energy + |increment| ^ 2 / energy :=
      add_div _ _ _
    _ ≤ _ := add_le_add hFirst hSecond

/-- On the uniform radius `gap / 4`, every spectral mode lies strictly inside
the convergence disk of the square-root binomial series. -/
theorem productThroatDiracRelativeSquaredIncrement_abs_lt_one
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (mode : ProductThroatHeatMode data)
    (hIncrement : |increment| < productThroatDiracGap data / 4) :
    |productThroatDiracRelativeSquaredIncrement data center increment mode| < 1 := by
  have hGap := productThroatDiracGap_positive data
  have hFirst : 2 * |increment| / productThroatDiracGap data < (1 : ℝ) / 2 := by
    rw [div_lt_iff₀ hGap]
    nlinarith
  have hIncrementNonnegative : 0 ≤ |increment| := abs_nonneg _
  have hQuarterNonnegative : 0 ≤ productThroatDiracGap data / 4 := by positivity
  have hSq : |increment| ^ 2 < (productThroatDiracGap data / 4) ^ 2 :=
    (sq_lt_sq₀ hIncrementNonnegative hQuarterNonnegative).2 hIncrement
  have hSecond : |increment| ^ 2 / productThroatDiracGap data ^ 2 <
      (1 : ℝ) / 16 := by
    rw [div_lt_iff₀ (sq_pos_of_pos hGap)]
    nlinarith
  have hBound := productThroatDiracRelativeSquaredIncrement_abs_le
    data center increment mode
  nlinarith

/-- Consequently the binomial base `1 + relativeIncrement` stays positive on
the same uniform ball. -/
theorem productThroatDiracRelativeSquaredIncrement_one_add_positive
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (mode : ProductThroatHeatMode data)
    (hIncrement : |increment| < productThroatDiracGap data / 4) :
    0 < 1 + productThroatDiracRelativeSquaredIncrement
      data center increment mode := by
  have hAbs := productThroatDiracRelativeSquaredIncrement_abs_lt_one
    data center increment mode hIncrement
  linarith [neg_lt_of_abs_lt hAbs]

/-- Mode-independent majorant of the relative squared increment. -/
def productThroatDiracRelativeSquaredIncrementBound
    (data : ProductThroatSpectralData) (increment : ℝ) : ℝ :=
  2 * |increment| / productThroatDiracGap data +
    |increment| ^ 2 / productThroatDiracGap data ^ 2

theorem productThroatDiracRelativeSquaredIncrementBound_nonnegative
    (data : ProductThroatSpectralData) (increment : ℝ) :
    0 ≤ productThroatDiracRelativeSquaredIncrementBound data increment := by
  unfold productThroatDiracRelativeSquaredIncrementBound
  have hGap := (productThroatDiracGap_positive data).le
  exact add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (abs_nonneg increment)) hGap)
    (div_nonneg (sq_nonneg |increment|) (sq_nonneg _))

theorem productThroatDiracRelativeSquaredIncrementBound_lt_one
    (data : ProductThroatSpectralData) (increment : ℝ)
    (hIncrement : |increment| < productThroatDiracGap data / 4) :
    productThroatDiracRelativeSquaredIncrementBound data increment < 1 := by
  have hGap := productThroatDiracGap_positive data
  have hFirst : 2 * |increment| / productThroatDiracGap data < (1 : ℝ) / 2 := by
    rw [div_lt_iff₀ hGap]
    nlinarith
  have hIncrementNonnegative : 0 ≤ |increment| := abs_nonneg _
  have hQuarterNonnegative : 0 ≤ productThroatDiracGap data / 4 := by positivity
  have hSq : |increment| ^ 2 < (productThroatDiracGap data / 4) ^ 2 :=
    (sq_lt_sq₀ hIncrementNonnegative hQuarterNonnegative).2 hIncrement
  have hSecond : |increment| ^ 2 / productThroatDiracGap data ^ 2 <
      (1 : ℝ) / 16 := by
    rw [div_lt_iff₀ (sq_pos_of_pos hGap)]
    nlinarith
  unfold productThroatDiracRelativeSquaredIncrementBound
  nlinarith

/-- The relative squared increment as a diagonal multiplier on the full
product Hilbert space. -/
def productThroatDiracRelativeSquaredIncrementImage
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (state : ProductThroatHeatHilbert data) : ProductThroatHeatHilbert data := by
  let bound := productThroatDiracRelativeSquaredIncrementBound data increment
  let image : ProductThroatHeatMode data → Complex := fun mode =>
    (productThroatDiracRelativeSquaredIncrement data center increment mode : Complex) *
      state mode
  have hBound : 0 ≤ bound :=
    productThroatDiracRelativeSquaredIncrementBound_nonnegative data increment
  have hMajorant : Memℓp
      (fun mode => (bound : Complex) * state mode) 2 :=
    (lp.memℓp state).const_mul (bound : Complex)
  have hImage : Memℓp image 2 := hMajorant.mono' (fun mode => by
    rw [show image mode =
        (productThroatDiracRelativeSquaredIncrement data center increment mode : Complex) *
          state mode by rfl,
      norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hBound]
    exact mul_le_mul_of_nonneg_right
      (productThroatDiracRelativeSquaredIncrement_abs_le
        data center increment mode) (norm_nonneg _))
  exact ⟨image, hImage⟩

@[simp]
theorem productThroatDiracRelativeSquaredIncrementImage_apply
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (state : ProductThroatHeatHilbert data) (mode : ProductThroatHeatMode data) :
    productThroatDiracRelativeSquaredIncrementImage data center increment state mode =
      (productThroatDiracRelativeSquaredIncrement data center increment mode : Complex) *
        state mode :=
  rfl

theorem productThroatDiracRelativeSquaredIncrementImage_norm_le
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (state : ProductThroatHeatHilbert data) :
    ‖productThroatDiracRelativeSquaredIncrementImage
        data center increment state‖ ≤
      productThroatDiracRelativeSquaredIncrementBound data increment * ‖state‖ := by
  have hBound :=
    productThroatDiracRelativeSquaredIncrementBound_nonnegative data increment
  calc
    _ ≤ ‖((productThroatDiracRelativeSquaredIncrementBound data increment : ℝ) :
          Complex) • state‖ := lp.norm_mono (by norm_num) (fun mode => by
      change ‖(productThroatDiracRelativeSquaredIncrement
          data center increment mode : Complex) * state mode‖ ≤
        ‖((productThroatDiracRelativeSquaredIncrementBound data increment : ℝ) :
          Complex) * state mode‖
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hBound]
      exact mul_le_mul_of_nonneg_right
        (productThroatDiracRelativeSquaredIncrement_abs_le
          data center increment mode) (norm_nonneg _))
    _ = _ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBound]

/-- Bounded diagonal operator of relative squared increments. -/
def productThroatDiracRelativeSquaredIncrementOperator
    (data : ProductThroatSpectralData) (center increment : ℝ) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  LinearMap.mkContinuous
    { toFun := productThroatDiracRelativeSquaredIncrementImage data center increment
      map_add' := by
        intro first second
        ext mode
        simp [productThroatDiracRelativeSquaredIncrementImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [productThroatDiracRelativeSquaredIncrementImage_apply]
        ring }
    (productThroatDiracRelativeSquaredIncrementBound data increment)
    (productThroatDiracRelativeSquaredIncrementImage_norm_le
      data center increment)

@[simp]
theorem productThroatDiracRelativeSquaredIncrementOperator_apply
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (state : ProductThroatHeatHilbert data) (mode : ProductThroatHeatMode data) :
    productThroatDiracRelativeSquaredIncrementOperator data center increment
        state mode =
      (productThroatDiracRelativeSquaredIncrement data center increment mode : Complex) *
        state mode :=
  rfl

theorem productThroatDiracRelativeSquaredIncrementOperator_norm_le
    (data : ProductThroatSpectralData) (center increment : ℝ) :
    ‖productThroatDiracRelativeSquaredIncrementOperator data center increment‖ ≤
      productThroatDiracRelativeSquaredIncrementBound data increment := by
  apply LinearMap.mkContinuous_norm_le
  exact productThroatDiracRelativeSquaredIncrementBound_nonnegative data increment

theorem productThroatDiracRelativeSquaredIncrementOperator_norm_lt_one
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (hIncrement : |increment| < productThroatDiracGap data / 4) :
    ‖productThroatDiracRelativeSquaredIncrementOperator data center increment‖ < 1 :=
  lt_of_le_of_lt
    (productThroatDiracRelativeSquaredIncrementOperator_norm_le
      data center increment)
    (productThroatDiracRelativeSquaredIncrementBound_lt_one
      data increment hIncrement)

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

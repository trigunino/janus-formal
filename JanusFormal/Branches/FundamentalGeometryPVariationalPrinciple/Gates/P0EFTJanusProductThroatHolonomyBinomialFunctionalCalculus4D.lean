import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyDerivative4D
import Mathlib.Analysis.Analytic.Binomial

/-!
# Uniform binomial functional calculus for the product holonomy family

On the mode-independent ball of radius `gap / 4`, the relative squared
increment has operator norm below one.  Hence the square-root binomial series
converges absolutely in operator norm.  Its sum is identified on every mode
with the positive scalar square root.  This replaces further order-by-order
differentiation by one convergent functional-calculus object.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyBinomialFunctionalCalculus4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open scoped ENNReal lp

/-- The `n`th operator term of the square-root binomial series. -/
def productThroatDiracBinomialSqrtOperatorTerm
    (data : ProductThroatSpectralData) (center increment : ℝ) (n : ℕ) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  ((Ring.choose ((1 : ℝ) / 2) n : ℝ) : Complex) •
    (productThroatDiracRelativeSquaredIncrementOperator data center increment) ^ n

/-- Absolute convergence of the binomial series in operator norm on the
uniform spectral ball. -/
theorem productThroatDiracBinomialSqrtOperatorTerm_summable
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (hIncrement : |increment| < productThroatDiracGap data / 4) :
    Summable (productThroatDiracBinomialSqrtOperatorTerm
      data center increment) := by
  let operator := productThroatDiracRelativeSquaredIncrementOperator
    data center increment
  let series := binomialSeries ℝ ((1 : ℝ) / 2)
  let radius : NNReal := ⟨‖operator‖, norm_nonneg operator⟩
  have hOperator : ‖operator‖ < 1 :=
    productThroatDiracRelativeSquaredIncrementOperator_norm_lt_one
      data center increment hIncrement
  have hRadius : (radius : ENNReal) < 1 := by
    exact_mod_cast hOperator
  have hSeriesRadius : (radius : ENNReal) < series.radius :=
    lt_of_lt_of_le hRadius binomialSeries_radius_ge_one
  have hScalar := series.summable_norm_mul_pow hSeriesRadius
  apply Summable.of_norm_bounded hScalar
  intro n
  have hPower : ‖operator ^ n‖ ≤ ‖operator‖ ^ n := by
    induction n with
    | zero =>
        rw [pow_zero, pow_zero]
        change ‖ContinuousLinearMap.id Complex
          (ProductThroatHeatHilbert data)‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
          (mul_le_mul_of_nonneg_right ih (norm_nonneg operator))
  unfold productThroatDiracBinomialSqrtOperatorTerm
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |Ring.choose ((1 : ℝ) / 2) n| * ‖operator ^ n‖ ≤
        |Ring.choose ((1 : ℝ) / 2) n| * ‖operator‖ ^ n :=
      mul_le_mul_of_nonneg_left hPower (abs_nonneg _)
    _ = ‖series n‖ * (radius : ℝ) ^ n := by
      have hCoefficient : |Ring.choose ((1 : ℝ) / 2) n| = ‖series n‖ := by
        simp [series, binomialSeries, Real.norm_eq_abs]
      rw [hCoefficient]
      rfl

/-- Powers of the relative diagonal operator remain diagonal with the expected
scalar powers. -/
theorem productThroatDiracRelativeSquaredIncrementOperator_pow_apply
    (data : ProductThroatSpectralData) (center increment : ℝ) (n : ℕ)
    (state : ProductThroatHeatHilbert data) (mode : ProductThroatHeatMode data) :
    ((productThroatDiracRelativeSquaredIncrementOperator data center increment) ^ n)
        state mode =
      (productThroatDiracRelativeSquaredIncrement data center increment mode : Complex) ^ n *
        state mode := by
  induction n generalizing state with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, mul_apply_eq_comp, ih,
        productThroatDiracRelativeSquaredIncrementOperator_apply]
      ring

@[simp]
theorem productThroatDiracBinomialSqrtOperatorTerm_apply
    (data : ProductThroatSpectralData) (center increment : ℝ) (n : ℕ)
    (state : ProductThroatHeatHilbert data) (mode : ProductThroatHeatMode data) :
    productThroatDiracBinomialSqrtOperatorTerm data center increment n state mode =
      ((Ring.choose ((1 : ℝ) / 2) n : ℝ) : Complex) *
        (productThroatDiracRelativeSquaredIncrement data center increment mode : Complex) ^ n *
          state mode := by
  unfold productThroatDiracBinomialSqrtOperatorTerm
  change (((Ring.choose ((1 : ℝ) / 2) n : ℝ) : Complex) *
      (((productThroatDiracRelativeSquaredIncrementOperator
        data center increment) ^ n) state mode)) = _
  rw [productThroatDiracRelativeSquaredIncrementOperator_pow_apply]
  ring

/-- Operator-norm sum of the positive square-root binomial series. -/
def productThroatDiracBinomialSqrtOperator
    (data : ProductThroatSpectralData) (center increment : ℝ) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  ∑' n, productThroatDiracBinomialSqrtOperatorTerm data center increment n

/-- The operator series is exactly the positive square root of `1 + relative`
on every spectral mode. -/
theorem productThroatDiracBinomialSqrtOperator_apply
    (data : ProductThroatSpectralData) (center increment : ℝ)
    (hIncrement : |increment| < productThroatDiracGap data / 4)
    (state : ProductThroatHeatHilbert data) (mode : ProductThroatHeatMode data) :
    productThroatDiracBinomialSqrtOperator data center increment state mode =
      (Real.sqrt (1 + productThroatDiracRelativeSquaredIncrement
        data center increment mode) : Complex) * state mode := by
  let evalState := (ContinuousLinearMap.apply Complex
    (ProductThroatHeatHilbert data)) state
  let evalMode := lp.evalCLM Complex
    (fun _ : ProductThroatHeatMode data => Complex) 2 mode
  let evaluation := evalMode.comp evalState
  have hOperatorSummable :=
    productThroatDiracBinomialSqrtOperatorTerm_summable
      data center increment hIncrement
  have hEvaluation := evaluation.map_tsum hOperatorSummable
  have hOperatorExpansion :
      productThroatDiracBinomialSqrtOperator data center increment state mode =
        ∑' n, productThroatDiracBinomialSqrtOperatorTerm
          data center increment n state mode := by
    change evaluation
      (∑' n, productThroatDiracBinomialSqrtOperatorTerm data center increment n) = _
    exact hEvaluation
  rw [hOperatorExpansion]
  have hRelative := productThroatDiracRelativeSquaredIncrement_abs_lt_one
    data center increment mode hIncrement
  have hBall : productThroatDiracRelativeSquaredIncrement data center increment mode ∈
      Metric.eball (0 : ℝ) 1 := by
    rw [mem_eball_zero_iff]
    change ‖productThroatDiracRelativeSquaredIncrement
      data center increment mode‖ₑ < ((1 : NNReal) : ENNReal)
    rw [enorm_lt_coe]
    exact_mod_cast (show
      ‖productThroatDiracRelativeSquaredIncrement data center increment mode‖ <
        (1 : ℝ) by simpa [Real.norm_eq_abs] using hRelative)
  have hScalar :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := (1 : ℝ) / 2)).hasSum hBall
  have hScalar' : HasSum
      (fun n => Ring.choose ((1 : ℝ) / 2) n *
        productThroatDiracRelativeSquaredIncrement data center increment mode ^ n)
      (Real.sqrt (1 + productThroatDiracRelativeSquaredIncrement
        data center increment mode)) := by
    have hTerms := hScalar.congr_fun (fun n => by
      rw [binomialSeries_apply])
    simpa only [zero_add, ← Real.sqrt_eq_rpow, smul_eq_mul,
      List.prod_ofFn, Fin.prod_const] using hTerms
  have hComplexMapped := hScalar'.map Complex.ofRealCLM
    Complex.ofRealCLM.continuous
  have hComplex : HasSum
      (fun n => ((Ring.choose ((1 : ℝ) / 2) n *
        productThroatDiracRelativeSquaredIncrement data center increment mode ^ n : ℝ) :
          Complex) * state mode)
      ((Real.sqrt (1 + productThroatDiracRelativeSquaredIncrement
        data center increment mode) : Complex) * state mode) := by
    simpa using hComplexMapped.mul_right (state mode)
  have hTerms : HasSum
      (fun n => productThroatDiracBinomialSqrtOperatorTerm
        data center increment n state mode)
      ((Real.sqrt (1 + productThroatDiracRelativeSquaredIncrement
        data center increment mode) : Complex) * state mode) := by
    convert hComplex using 1
    funext n
    rw [productThroatDiracBinomialSqrtOperatorTerm_apply]
    norm_cast
  exact hTerms.tsum_eq

end

end P0EFTJanusProductThroatHolonomyBinomialFunctionalCalculus4D
end JanusFormal

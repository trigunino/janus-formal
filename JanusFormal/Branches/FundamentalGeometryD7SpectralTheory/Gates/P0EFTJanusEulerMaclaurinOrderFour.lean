import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace JanusFormal
namespace P0EFTJanusEulerMaclaurinOrderFour

set_option autoImplicit false

open Set MeasureTheory Filter

noncomputable section

/-- The normalized Bernoulli kernels used in the order-four Euler--Maclaurin formula. -/
def b1 (x : ℝ) : ℝ := x - 1 / 2
def b2 (x : ℝ) : ℝ := x ^ 2 / 2 - x / 2 + 1 / 12
def b3 (x : ℝ) : ℝ := x ^ 3 / 6 - x ^ 2 / 4 + x / 12
def b4 (x : ℝ) : ℝ := x ^ 4 / 24 - x ^ 3 / 12 + x ^ 2 / 24 - 1 / 720
def b5 (x : ℝ) : ℝ := x ^ 5 / 120 - x ^ 4 / 48 + x ^ 3 / 72 - x / 720

@[simp] theorem b1_zero : b1 0 = -(1 / 2 : ℝ) := by norm_num [b1]
@[simp] theorem b1_one : b1 1 = (1 / 2 : ℝ) := by norm_num [b1]
@[simp] theorem b2_zero : b2 0 = (1 / 12 : ℝ) := by norm_num [b2]
@[simp] theorem b2_one : b2 1 = (1 / 12 : ℝ) := by norm_num [b2]
@[simp] theorem b3_zero : b3 0 = 0 := by norm_num [b3]
@[simp] theorem b3_one : b3 1 = 0 := by norm_num [b3]
@[simp] theorem b4_zero : b4 0 = -(1 / 720 : ℝ) := by norm_num [b4]
@[simp] theorem b4_one : b4 1 = -(1 / 720 : ℝ) := by norm_num [b4]
@[simp] theorem b5_zero : b5 0 = 0 := by norm_num [b5]
@[simp] theorem b5_one : b5 1 = 0 := by norm_num [b5]

theorem hasDerivAt_b1 (x : ℝ) : HasDerivAt b1 1 x := by
  unfold b1
  convert (hasDerivAt_id x).sub_const (1 / 2) using 1
  all_goals rfl

theorem hasDerivAt_b2 (x : ℝ) : HasDerivAt b2 (b1 x) x := by
  unfold b1 b2
  convert ((hasDerivAt_pow 2 x).div_const 2 |>.sub
    ((hasDerivAt_id x).div_const 2) |>.add_const (1 / 12)) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_b3 (x : ℝ) : HasDerivAt b3 (b2 x) x := by
  unfold b2 b3
  convert ((hasDerivAt_pow 3 x).div_const 6 |>.sub
    ((hasDerivAt_pow 2 x).div_const 4) |>.add
      ((hasDerivAt_id x).div_const 12)) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_b4 (x : ℝ) : HasDerivAt b4 (b3 x) x := by
  unfold b3 b4
  convert ((hasDerivAt_pow 4 x).div_const 24 |>.sub
    ((hasDerivAt_pow 3 x).div_const 12) |>.add
      ((hasDerivAt_pow 2 x).div_const 24) |>.sub_const (1 / 720)) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_b5 (x : ℝ) : HasDerivAt b5 (b4 x) x := by
  unfold b4 b5
  convert ((hasDerivAt_pow 5 x).div_const 120 |>.sub
    ((hasDerivAt_pow 4 x).div_const 48) |>.add
      ((hasDerivAt_pow 3 x).div_const 72) |>.sub
        ((hasDerivAt_id x).div_const 720)) using 1
  all_goals first | rfl | ring

theorem abs_b5_le_one {x : ℝ} (hx : x ∈ Icc 0 1) : |b5 x| ≤ 1 := by
  have hxabs : |x| ≤ 1 := by simpa [abs_of_nonneg hx.1] using hx.2
  have hp (n : ℕ) : |x ^ n| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_one₀ (abs_nonneg x) hxabs
  have h120 : |(120 : ℝ)| = 120 := by norm_num
  have h48 : |(48 : ℝ)| = 48 := by norm_num
  have h72 : |(72 : ℝ)| = 72 := by norm_num
  have h720 : |(720 : ℝ)| = 720 := by norm_num
  unfold b5
  calc
    |x ^ 5 / 120 - x ^ 4 / 48 + x ^ 3 / 72 - x / 720| ≤
        |x ^ 5 / 120| + |x ^ 4 / 48| + |x ^ 3 / 72| + |x / 720| := by
          calc
            _ ≤ |x ^ 5 / 120 - x ^ 4 / 48 + x ^ 3 / 72| + |x / 720| := abs_sub _ _
            _ ≤ (|x ^ 5 / 120 - x ^ 4 / 48| + |x ^ 3 / 72|) + |x / 720| := by
              gcongr
              exact abs_add_le _ _
            _ ≤ (|x ^ 5 / 120| + |x ^ 4 / 48|) + |x ^ 3 / 72| + |x / 720| := by
              gcongr
              exact abs_sub _ _
    _ ≤ 1 / 120 + 1 / 48 + 1 / 72 + 1 / 720 := by
      simp only [abs_div, h120, h48, h72, h720]
      gcongr
      · exact hp 5
      · exact hp 4
      · exact hp 3
    _ ≤ 1 := by norm_num

/-- Exact Euler--Maclaurin identity on one unit cell, with the fifth derivative as remainder. -/
theorem euler_maclaurin_cell
    (f f1 f2 f3 f4 f5 : ℝ → ℝ) (a : ℝ)
    (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x)
    (h3 : ∀ x, HasDerivAt f2 (f3 x) x)
    (h4 : ∀ x, HasDerivAt f3 (f4 x) x)
    (h5 : ∀ x, HasDerivAt f4 (f5 x) x)
    (hcont5 : Continuous f5) :
    ∫ x in a..a + 1, f x =
      (f a + f (a + 1)) / 2 - (f1 (a + 1) - f1 a) / 12 +
        (f3 (a + 1) - f3 a) / 720 -
          ∫ x in a..a + 1, b5 (x - a) * f5 x := by
  have hb1 (x : ℝ) : HasDerivAt (fun y => b1 (y - a)) 1 x := by
    convert (hasDerivAt_b1 (x - a)).comp x ((hasDerivAt_id x).sub_const a) using 1
    all_goals first | rfl | ring
  have hb2 (x : ℝ) : HasDerivAt (fun y => b2 (y - a)) (b1 (x - a)) x := by
    convert (hasDerivAt_b2 (x - a)).comp x ((hasDerivAt_id x).sub_const a) using 1
    all_goals first | rfl | ring
  have hb3 (x : ℝ) : HasDerivAt (fun y => b3 (y - a)) (b2 (x - a)) x := by
    convert (hasDerivAt_b3 (x - a)).comp x ((hasDerivAt_id x).sub_const a) using 1
    all_goals first | rfl | ring
  have hb4 (x : ℝ) : HasDerivAt (fun y => b4 (y - a)) (b3 (x - a)) x := by
    convert (hasDerivAt_b4 (x - a)).comp x ((hasDerivAt_id x).sub_const a) using 1
    all_goals first | rfl | ring
  have hb5 (x : ℝ) : HasDerivAt (fun y => b5 (y - a)) (b4 (x - a)) x := by
    convert (hasDerivAt_b5 (x - a)).comp x ((hasDerivAt_id x).sub_const a) using 1
    all_goals first | rfl | ring
  have hc1 : Continuous f1 := continuous_iff_continuousAt.2 fun x => (h2 x).continuousAt
  have hc2 : Continuous f2 := continuous_iff_continuousAt.2 fun x => (h3 x).continuousAt
  have hc3 : Continuous f3 := continuous_iff_continuousAt.2 fun x => (h4 x).continuousAt
  have hc4 : Continuous f4 := continuous_iff_continuousAt.2 fun x => (h5 x).continuousAt
  have hcb1 : Continuous (fun x => b1 (x - a)) :=
    continuous_iff_continuousAt.2 fun x => (hb1 x).continuousAt
  have hcb2 : Continuous (fun x => b2 (x - a)) :=
    continuous_iff_continuousAt.2 fun x => (hb2 x).continuousAt
  have hcb3 : Continuous (fun x => b3 (x - a)) :=
    continuous_iff_continuousAt.2 fun x => (hb3 x).continuousAt
  have hcb4 : Continuous (fun x => b4 (x - a)) :=
    continuous_iff_continuousAt.2 fun x => (hb4 x).continuousAt
  have hIBP1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1) (u := fun x => b1 (x - a)) (v := f)
    (u' := fun _ => 1) (v' := f1)
    (fun x _ => hb1 x) (fun x _ => h1 x)
    (continuous_const.intervalIntegrable _ _) hc1.continuousOn.intervalIntegrable
  have hIBP2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1) (u := fun x => b2 (x - a)) (v := f1)
    (u' := fun x => b1 (x - a)) (v' := f2)
    (fun x _ => hb2 x) (fun x _ => h2 x)
    hcb1.continuousOn.intervalIntegrable
    hc2.continuousOn.intervalIntegrable
  have hIBP3 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1) (u := fun x => b3 (x - a)) (v := f2)
    (u' := fun x => b2 (x - a)) (v' := f3)
    (fun x _ => hb3 x) (fun x _ => h3 x)
    hcb2.continuousOn.intervalIntegrable
    hc3.continuousOn.intervalIntegrable
  have hIBP4 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1) (u := fun x => b4 (x - a)) (v := f3)
    (u' := fun x => b3 (x - a)) (v' := f4)
    (fun x _ => hb4 x) (fun x _ => h4 x)
    hcb3.continuousOn.intervalIntegrable
    hc4.continuousOn.intervalIntegrable
  have hIBP5 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1) (u := fun x => b5 (x - a)) (v := f4)
    (u' := fun x => b4 (x - a)) (v' := f5)
    (fun x _ => hb5 x) (fun x _ => h5 x)
    hcb4.continuousOn.intervalIntegrable
    hcont5.continuousOn.intervalIntegrable
  simp only [sub_self, add_sub_cancel_left] at hIBP1 hIBP2 hIBP3 hIBP4 hIBP5
  simp only [b1_zero, b1_one, b2_zero, b2_one, b3_zero, b3_one,
    b4_zero, b4_one, b5_zero, b5_one] at hIBP1 hIBP2 hIBP3 hIBP4 hIBP5
  simp only [one_mul, zero_mul, zero_sub] at hIBP1 hIBP2 hIBP3 hIBP4 hIBP5
  linarith [hIBP1, hIBP2, hIBP3, hIBP4, hIBP5]

/-- Finite order-four Euler--Maclaurin formula on the nonnegative integer lattice. -/
theorem euler_maclaurin_finite
    (f f1 f2 f3 f4 f5 : ℝ → ℝ) (N : ℕ)
    (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x)
    (h3 : ∀ x, HasDerivAt f2 (f3 x) x)
    (h4 : ∀ x, HasDerivAt f3 (f4 x) x)
    (h5 : ∀ x, HasDerivAt f4 (f5 x) x)
    (hcont5 : Continuous f5) :
    (∑ n ∈ Finset.range N, f (n : ℝ)) - f 0 / 2 + f (N : ℝ) / 2 =
      (∫ x in (0 : ℝ)..(N : ℝ), f x) + (f1 (N : ℝ) - f1 0) / 12 -
        (f3 (N : ℝ) - f3 0) / 720 +
          ∑ n ∈ Finset.range N,
            ∫ x in (n : ℝ)..(n : ℝ) + 1, b5 (x - n) * f5 x := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hc : Continuous f := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
      have hInt := intervalIntegral.integral_add_adjacent_intervals
        (f := f) (μ := volume) (a := (0 : ℝ)) (b := (N : ℝ)) (c := (N : ℝ) + 1)
        hc.continuousOn.intervalIntegrable hc.continuousOn.intervalIntegrable
      have hCell := euler_maclaurin_cell f f1 f2 f3 f4 f5 (N : ℝ)
        h1 h2 h3 h4 h5 hcont5
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
      rw [← hInt]
      rw [hCell]
      linear_combination ih

/-- The finite remainder is bounded by the `L¹` norm of the fifth derivative. -/
theorem euler_maclaurin_finite_remainder_bound
    (f5 : ℝ → ℝ) (N : ℕ) (hcont5 : Continuous f5) :
    |∑ n ∈ Finset.range N,
        ∫ x in (n : ℝ)..(n : ℝ) + 1, b5 (x - n) * f5 x| ≤
      ∫ x in (0 : ℝ)..(N : ℝ), |f5 x| := by
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        |∫ x in (n : ℝ)..(n : ℝ) + 1, b5 (x - n) * f5 x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N,
        ∫ x in (n : ℝ)..(n : ℝ) + 1, |f5 x| := by
      apply Finset.sum_le_sum
      intro n hn
      have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by norm_num
      have hb5cont : Continuous (fun x : ℝ => b5 (x - (n : ℝ))) := by
        unfold b5
        fun_prop
      refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
      apply intervalIntegral.integral_mono_on hle
        ((hb5cont.mul hcont5).abs.intervalIntegrable _ _)
        (hcont5.abs.intervalIntegrable _ _)
      intro x hx
      change |b5 (x - (n : ℝ)) * f5 x| ≤ |f5 x|
      rw [abs_mul]
      have ht : x - (n : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_b5_le_one ht)
    _ = _ := by
      convert intervalIntegral.sum_integral_adjacent_intervals
        (f := fun x : ℝ => |f5 x|) (μ := volume) (a := fun n : ℕ => (n : ℝ))
        (n := N) (fun k hk => hcont5.abs.intervalIntegrable _ _) using 1 <;>
        simp [Nat.cast_add]

/-- Infinite order-four Euler--Maclaurin estimate obtained from the finite identity. -/
theorem euler_maclaurin_tsum_error_bound
    (f f1 f2 f3 f4 f5 : ℝ → ℝ) (integralValue errorBound : ℝ)
    (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x)
    (h3 : ∀ x, HasDerivAt f2 (f3 x) x)
    (h4 : ∀ x, HasDerivAt f3 (f4 x) x)
    (h5 : ∀ x, HasDerivAt f4 (f5 x) x)
    (hcont5 : Continuous f5)
    (hsum : Summable (fun n : ℕ => f (n : ℝ)))
    (hIntegral : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), f x)
      Filter.atTop (nhds integralValue))
    (hAtTop : Tendsto (fun N : ℕ => f (N : ℝ)) Filter.atTop (nhds 0))
    (h1AtTop : Tendsto (fun N : ℕ => f1 (N : ℝ)) Filter.atTop (nhds 0))
    (h3AtTop : Tendsto (fun N : ℕ => f3 (N : ℝ)) Filter.atTop (nhds 0))
    (hError : ∀ N : ℕ, (∫ x in (0 : ℝ)..(N : ℝ), |f5 x|) ≤ errorBound) :
    |∑' n : ℕ, f (n : ℝ) - f 0 / 2 - integralValue + f1 0 / 12 - f3 0 / 720| ≤
      errorBound := by
  let E : ℕ → ℝ := fun N =>
    (∑ n ∈ Finset.range N, f (n : ℝ)) - f 0 / 2 + f (N : ℝ) / 2 -
      (∫ x in (0 : ℝ)..(N : ℝ), f x) - (f1 (N : ℝ) - f1 0) / 12 +
        (f3 (N : ℝ) - f3 0) / 720
  have hELimit : Tendsto E Filter.atTop
      (nhds (∑' n : ℕ, f (n : ℝ) - f 0 / 2 - integralValue + f1 0 / 12 - f3 0 / 720)) := by
    have hs := hsum.hasSum.tendsto_sum_nat
    have h := ((((hs.sub_const (f 0 / 2)).add (hAtTop.div_const 2)).sub hIntegral).sub
      ((h1AtTop.sub_const (f1 0)).div_const 12)).add
        ((h3AtTop.sub_const (f3 0)).div_const 720)
    convert h using 1
    simp
    ring
  have hEach (N : ℕ) : |E N| ≤ errorBound := by
    have hFinite := euler_maclaurin_finite f f1 f2 f3 f4 f5 N
      h1 h2 h3 h4 h5 hcont5
    have hEq : E N = ∑ n ∈ Finset.range N,
        ∫ x in (n : ℝ)..(n : ℝ) + 1, b5 (x - n) * f5 x := by
      dsimp [E]
      linear_combination hFinite
    rw [hEq]
    exact (euler_maclaurin_finite_remainder_bound f5 N hcont5).trans (hError N)
  exact le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hELimit)
    (Eventually.of_forall hEach)

end

end P0EFTJanusEulerMaclaurinOrderFour
end JanusFormal

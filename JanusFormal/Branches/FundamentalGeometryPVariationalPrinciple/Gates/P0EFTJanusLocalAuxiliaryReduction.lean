import Mathlib

/-!
# A local auxiliary symbol can have a nonpolynomial Schur reduction

This scalar constant-coefficient toy model fixes the nonnegative symbol variable
`s`, a positive squared mass `m2`, a constant coupling `b`, and a polynomial
boundary symbol `c`. The local parent has auxiliary symbol `m2 + s`.
Its exact Schur reduction is nonpolynomial for nonzero coupling, while its
first-order derivative expansion has an explicit, bounded remainder.

These are symbol-level statements, not a PDE existence result, a classification
of general local actions, or an identification of a physical Janus parent.
-/

namespace JanusFormal
namespace P0EFTJanusLocalAuxiliaryReduction

set_option autoImplicit false

/-- Quadratic local parent at a fixed nonnegative differential symbol. -/
noncomputable def localParentAction
    (m2 b : ℝ) (c : Polynomial ℝ) (s auxiliary boundary : ℝ) : ℝ :=
  (m2 + s) * auxiliary ^ 2 / 2 + b * auxiliary * boundary +
    c.eval s * boundary ^ 2 / 2

/-- Exact rational Schur symbol obtained by eliminating the auxiliary. -/
noncomputable def reducedSymbol
    (m2 b : ℝ) (c : Polynomial ℝ) (s : ℝ) : ℝ :=
  c.eval s - b ^ 2 / (m2 + s)

theorem auxiliary_stationary_solution
    (m2 b s boundary : ℝ) (hm : 0 < m2) (hs : 0 ≤ s) :
    (m2 + s) * (-b * boundary / (m2 + s)) + b * boundary = 0 := by
  have hd : m2 + s ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem eliminate_auxiliary
    (m2 b : ℝ) (c : Polynomial ℝ) (s boundary : ℝ)
    (hm : 0 < m2) (hs : 0 ≤ s) :
    localParentAction m2 b c s (-b * boundary / (m2 + s)) boundary =
      reducedSymbol m2 b c s * boundary ^ 2 / 2 := by
  have hd : m2 + s ≠ 0 := ne_of_gt (by linarith)
  unfold localParentAction reducedSymbol
  field_simp
  ring

/-- Even agreement only on physical nonnegative symbols forces an impossible
polynomial identity at the (negative) auxiliary pole. -/
theorem reduced_symbol_not_polynomial_on_nonnegative
    (m2 b : ℝ) (c : Polynomial ℝ) (hm : 0 < m2) (hb : b ≠ 0) :
    ¬ ∃ p : Polynomial ℝ, ∀ s : ℝ, 0 ≤ s →
      reducedSymbol m2 b c s = p.eval s := by
  rintro ⟨p, hp⟩
  have hpoly : (Polynomial.C m2 + Polynomial.X) * (c - p) =
      Polynomial.C (b ^ 2) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Ici_infinite (0 : ℝ)).mono
    intro s hs
    change 0 ≤ s at hs
    have hd : m2 + s ≠ 0 := ne_of_gt (by linarith)
    have heq := hp s hs
    unfold reducedSymbol at heq
    have hdiff : c.eval s - p.eval s = b ^ 2 / (m2 + s) := by linarith
    simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub]
    rw [hdiff]
    field_simp
  have hpole := congrArg (Polynomial.eval (-m2)) hpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, add_neg_cancel, zero_mul] at hpole
  exact hb (sq_eq_zero_iff.mp hpole.symm)

theorem inverse_symbol_first_order_identity
    (m2 s : ℝ) (hm : 0 < m2) (hs : 0 ≤ s) :
    1 / (m2 + s) = 1 / m2 - s / m2 ^ 2 +
      s ^ 2 / (m2 ^ 2 * (m2 + s)) := by
  have hm0 : m2 ≠ 0 := ne_of_gt hm
  have hd : m2 + s ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- Retain the constant and linear terms of the inverse auxiliary symbol. -/
noncomputable def firstOrderLocalSymbol
    (m2 b : ℝ) (c : Polynomial ℝ) : Polynomial ℝ :=
  c - Polynomial.C (b ^ 2 / m2) +
    Polynomial.C (b ^ 2 / m2 ^ 2) * Polynomial.X

theorem reduced_symbol_exact_remainder
    (m2 b : ℝ) (c : Polynomial ℝ) (s : ℝ)
    (hm : 0 < m2) (hs : 0 ≤ s) :
    reducedSymbol m2 b c s = (firstOrderLocalSymbol m2 b c).eval s -
      b ^ 2 * s ^ 2 / (m2 ^ 2 * (m2 + s)) := by
  have hm0 : m2 ≠ 0 := ne_of_gt hm
  have hd : m2 + s ≠ 0 := ne_of_gt (by linarith)
  simp only [reducedSymbol, firstOrderLocalSymbol, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  field_simp
  ring

/-- The approximation overestimates the exact response, with a quadratic
error bound valid for every nonnegative symbol. -/
theorem first_order_error_bounds
    (m2 b : ℝ) (c : Polynomial ℝ) (s : ℝ)
    (hm : 0 < m2) (hs : 0 ≤ s) :
    0 ≤ (firstOrderLocalSymbol m2 b c).eval s - reducedSymbol m2 b c s ∧
    (firstOrderLocalSymbol m2 b c).eval s - reducedSymbol m2 b c s ≤
      b ^ 2 * s ^ 2 / m2 ^ 3 := by
  rw [reduced_symbol_exact_remainder m2 b c s hm hs]
  have hnum : 0 ≤ b ^ 2 * s ^ 2 := mul_nonneg (sq_nonneg b) (sq_nonneg s)
  have hden : 0 < m2 ^ 2 * (m2 + s) := by positivity
  have hden0 : 0 < m2 ^ 3 := by positivity
  have hdenle : m2 ^ 3 ≤ m2 ^ 2 * (m2 + s) := by
    nlinarith [mul_nonneg (sq_nonneg m2) hs]
  constructor
  · simpa using div_nonneg hnum hden.le
  · simpa using div_le_div_of_nonneg_left hnum hden0 hdenle

/-- On a low-frequency band `s ≤ ε m2`, the absolute error is at most
`(b² / m2) ε²`. Thus the expansion has a controlled domain of validity. -/
theorem first_order_uniform_band_error
    (m2 b : ℝ) (c : Polynomial ℝ) (s ε : ℝ)
    (hm : 0 < m2) (hs : 0 ≤ s) (hε : 0 ≤ ε) (hband : s ≤ ε * m2) :
    |reducedSymbol m2 b c s - (firstOrderLocalSymbol m2 b c).eval s| ≤
      (b ^ 2 / m2) * ε ^ 2 := by
  have herr := first_order_error_bounds m2 b c s hm hs
  rw [abs_sub_comm, abs_of_nonneg herr.1]
  have hsquare : s ^ 2 ≤ ε ^ 2 * m2 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hband)
      (show 0 ≤ ε * m2 + s by positivity)]
  have hm0 : m2 ≠ 0 := ne_of_gt hm
  calc
    (firstOrderLocalSymbol m2 b c).eval s - reducedSymbol m2 b c s ≤
        b ^ 2 * s ^ 2 / m2 ^ 3 := herr.2
    _ ≤ b ^ 2 * (ε ^ 2 * m2 ^ 2) / m2 ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare (sq_nonneg b)) (by positivity)
    _ = (b ^ 2 / m2) * ε ^ 2 := by field_simp

end P0EFTJanusLocalAuxiliaryReduction
end JanusFormal

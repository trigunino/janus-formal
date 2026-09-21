import Mathlib

/-!
# Exact local gluing preserves an unselected mass-type parameter

A nearest-neighbor segment has action `a(x²+y²)/2-bxy`, with `a>b>0`.
Segments with the same `d=a²-b²` glue by stationary elimination into another
segment with that d, and gluing is associative. Different positive d remain
admissible even after fixing the elementary mixed coupling b=1. Thus exact
classical gluing and positivity do not select this parameter, independently
of overall action normalization. Endpoint traces are marked and held fixed.
This is a finite local model, not a Janus PDE.
-/

namespace JanusFormal
namespace P0EFTJanusT08LocalGluingSelectionFreedom

set_option autoImplicit false
noncomputable section

@[ext] structure Segment (d : ℝ) where
  a : ℝ
  b : ℝ
  b_pos : 0 < b
  gap : b < a
  invariant : a ^ 2 - b ^ 2 = d

variable {d : ℝ}

theorem Segment.a_pos (p : Segment d) : 0 < p.a := lt_trans p.b_pos p.gap

theorem Segment.parameter_pos (p : Segment d) : 0 < d := by
  have h := mul_pos (sub_pos.mpr p.gap) (add_pos p.a_pos p.b_pos)
  nlinarith [p.invariant]

def action (p : Segment d) (x y : ℝ) : ℝ := p.a * (x ^ 2 + y ^ 2) / 2 - p.b * x * y

theorem action_square_decomposition (p : Segment d) (x y : ℝ) :
    action p x y = (p.a - p.b) * (x ^ 2 + y ^ 2) / 2 + p.b * (x - y) ^ 2 / 2 := by
  unfold action
  ring

theorem action_positive (p : Segment d) (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    0 < action p x y := by
  rw [action_square_decomposition]
  have hs : 0 < x ^ 2 + y ^ 2 := by
    rcases h with hx | hy
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hy)
  have hmain := mul_pos (sub_pos.mpr p.gap) hs
  have hrest := mul_nonneg p.b_pos.le (sq_nonneg (x - y))
  linarith

theorem action_sign_invariant (p : Segment d) (x y : ℝ) :
    action p (-x) (-y) = action p x y := by unfold action; ring

theorem action_endpoint_reversal (p : Segment d) (x y : ℝ) :
    action p y x = action p x y := by unfold action; ring

theorem gluing_sum_pos (p q : Segment d) : 0 < p.a + q.a := add_pos p.a_pos q.a_pos

/-- Exact composition of two equal-parameter local segments. -/
def glue (p q : Segment d) : Segment d where
  a := (p.a * q.a + d) / (p.a + q.a)
  b := (p.b * q.b) / (p.a + q.a)
  b_pos := div_pos (mul_pos p.b_pos q.b_pos) (gluing_sum_pos p q)
  gap := by
    apply (div_lt_div_iff_of_pos_right (gluing_sum_pos p q)).2
    have hm : p.b * q.b < p.a * q.a :=
      lt_trans (mul_lt_mul_of_pos_right p.gap q.b_pos)
        (mul_lt_mul_of_pos_left q.gap p.a_pos)
    linarith [p.parameter_pos]
  invariant := by
    have hp : p.b ^ 2 = p.a ^ 2 - d := by linarith [p.invariant]
    have hq : q.b ^ 2 = q.a ^ 2 - d := by linarith [q.invariant]
    have hs : p.a + q.a ≠ 0 := ne_of_gt (gluing_sum_pos p q)
    rw [div_pow, div_pow, ← sub_div, mul_pow, hp, hq]
    apply (div_eq_iff (pow_ne_zero 2 hs)).2
    ring

def stationaryMiddle (p q : Segment d) (x y : ℝ) : ℝ :=
  (p.b * x + q.b * y) / (p.a + q.a)

theorem stationary_middle_unique (p q : Segment d) (x y z : ℝ) :
    (p.a + q.a) * z - p.b * x - q.b * y = 0 ↔ z = stationaryMiddle p q x y := by
  rw [stationaryMiddle, eq_div_iff (ne_of_gt (gluing_sum_pos p q))]
  constructor <;> intro h <;> linarith

/-- The Schur formula is derived from the sum of two local actions. -/
theorem stationary_gluing_action (p q : Segment d) (x y : ℝ) :
    action p x (stationaryMiddle p q x y) + action q (stationaryMiddle p q x y) y =
      action (glue p q) x y := by
  have hp : p.b ^ 2 = p.a ^ 2 - d := by linarith [p.invariant]
  have hq : q.b ^ 2 = q.a ^ 2 - d := by linarith [q.invariant]
  have hs : p.a + q.a ≠ 0 := ne_of_gt (gluing_sum_pos p q)
  unfold action stationaryMiddle glue
  field_simp
  ring_nf
  simp only [hp, hq]
  ring

/-- Gluing order does not select the positive invariant d. -/
theorem glue_associative (p q r : Segment d) : glue (glue p q) r = glue p (glue q r) := by
  have hpq : p.a + q.a ≠ 0 := ne_of_gt (gluing_sum_pos p q)
  have hqr : q.a + r.a ≠ 0 := ne_of_gt (gluing_sum_pos q r)
  have hL : (glue p q).a + r.a ≠ 0 := ne_of_gt (gluing_sum_pos (glue p q) r)
  have hR : p.a + (glue q r).a ≠ 0 := ne_of_gt (gluing_sum_pos p (glue q r))
  ext <;> apply (div_eq_div_iff hL hR).2
  all_goals dsimp only [glue]
  all_goals field_simp [hpq, hqr]
  all_goals ring

/-- Every positive value of d admits an elementary segment with b fixed to one. -/
def normalizedSegment (d : ℝ) (hd : 0 < d) : Segment d where
  a := Real.sqrt (d + 1)
  b := 1
  b_pos := by norm_num
  gap := by
    have hs := Real.sq_sqrt (show 0 ≤ d + 1 by linarith)
    have hn := Real.sqrt_nonneg (d + 1)
    nlinarith
  invariant := by
    rw [Real.sq_sqrt (show 0 ≤ d + 1 by linarith)]
    ring

def firstSegment : Segment 3 where
  a := 2
  b := 1
  b_pos := by norm_num
  gap := by norm_num
  invariant := by norm_num

def secondSegment : Segment 8 where
  a := 3
  b := 1
  b_pos := by norm_num
  gap := by norm_num
  invariant := by norm_num

/-- Same elementary mixed normalization, distinct endpoint responses. Both
examples belong to positive, sign-symmetric, associative local gluing families. -/
theorem fixed_mixed_coupling_does_not_select_parameter :
    firstSegment.b = secondSegment.b ∧
      action firstSegment 1 0 ≠ action secondSegment 1 0 := by
  norm_num [firstSegment, secondSegment, action]

theorem examples_not_overall_rescalings :
    ¬ ∃ c : ℝ, ∀ x y : ℝ, action secondSegment x y = c * action firstSegment x y := by
  rintro ⟨c, hc⟩
  have h₁ := hc 1 0
  have h₂ := hc 1 1
  norm_num [firstSegment, secondSegment, action] at h₁ h₂
  linarith

/-- The difference persists on a closed periodic chain, where there is no
external boundary to absorb it as an endpoint counterterm. -/
theorem closed_chain_action_difference (x y z : ℝ) :
    (action secondSegment x y + action secondSegment y z + action secondSegment z x) -
      (action firstSegment x y + action firstSegment y z + action firstSegment z x) =
        x ^ 2 + y ^ 2 + z ^ 2 := by
  unfold action firstSegment secondSegment
  ring

end
end P0EFTJanusT08LocalGluingSelectionFreedom
end JanusFormal

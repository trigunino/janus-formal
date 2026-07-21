import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! # MF-SIGN-001: invariant versus sign-reversing involutions -/

namespace Janus.ProgramM

variable {α : Type*}

def InvolutionInvariant (σ : α → α) (charge : α → ℝ) : Prop :=
  ∀ x, charge (σ x) = charge x

def InvolutionOdd (σ : α → α) (charge : α → ℝ) : Prop :=
  ∀ x, charge (σ x) = -charge x

theorem involutionOdd_pair_sum_zero {σ : α → α} {charge : α → ℝ}
    (hodd : InvolutionOdd σ charge) (x : α) :
    charge x + charge (σ x) = 0 := by
  rw [hodd x]
  exact add_neg_cancel (charge x)

theorem invariant_and_odd_charge_zero {σ : α → α} {charge : α → ℝ}
    (hinvariant : InvolutionInvariant σ charge)
    (hodd : InvolutionOdd σ charge) (x : α) : charge x = 0 := by
  have h₁ := hinvariant x
  have h₂ := hodd x
  linarith

theorem involutionOdd_fixed_point_zero {σ : α → α} {charge : α → ℝ}
    (hodd : InvolutionOdd σ charge) {x : α} (hfixed : σ x = x) :
    charge x = 0 := by
  have h := hodd x
  rw [hfixed] at h
  linarith

end Janus.ProgramM

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Defs

/-! # MF-MEAS-001: uniform finite atomic measures are counting measures -/

namespace Janus.ProgramM

open scoped BigOperators

variable {α R : Type*} [AddCommMonoid R]

/-- A weight on objects that ignores every relabelling of the underlying set. -/
def FullyRelabellingInvariant (weight : α → R) : Prop :=
  ∀ (e : Equiv.Perm α) x, weight (e x) = weight x

omit [AddCommMonoid R] in
theorem fullyRelabellingInvariant_weight_eq [DecidableEq α] (weight : α → R)
    (h : FullyRelabellingInvariant weight) (base x : α) :
    weight x = weight base := by
  simpa using (h (Equiv.swap x base) x).symm

theorem uniformAtomicMass_eq_card_nsmul [DecidableEq α] (weight : α → R)
    (h : FullyRelabellingInvariant weight) (base : α) (s : Finset α) :
    (∑ x ∈ s, weight x) = s.card • weight base := by
  calc
    (∑ x ∈ s, weight x) = ∑ _x ∈ s, weight base := by
      apply Finset.sum_congr rfl
      intro x _
      exact fullyRelabellingInvariant_weight_eq weight h base x
    _ = s.card • weight base := by simp

end Janus.ProgramM

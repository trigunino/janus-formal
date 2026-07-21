import JanusFormal.Foundations.ProgramMErgodicLayerAdversary
import Mathlib.Order.Height

/-!
# MF-MAN-018: unbounded order height as a necessary ensemble diagnostic
-/

namespace JanusFormal.ProgramM

def HasUnboundedOrderHeight (height : ℕ → ℕ) : Prop :=
  ∀ bound, ∃ size, bound < height size

theorem bounded_height_not_unbounded (height : ℕ → ℕ) (bound : ℕ)
    (hbounded : ∀ size, height size ≤ bound) :
    ¬ HasUnboundedOrderHeight height := by
  intro hunbounded
  obtain ⟨size, hlarge⟩ := hunbounded bound
  exact (Nat.not_lt_of_ge (hbounded size)) hlarge

theorem six_level_height_not_unbounded (height : ℕ → ℕ)
    (hbounded : ∀ size, height size ≤ 6) :
    ¬ HasUnboundedOrderHeight height :=
  bounded_height_not_unbounded height 6 hbounded

/-- Mathlib's chain height is insensitive to reversing every arrow. -/
theorem chainHeight_orientation_invariant {α : Type*}
    (relation : α → α → Prop) (objects : Set α) :
    objects.chainHeight (flip relation) =
      objects.chainHeight relation := by
  exact Set.chainHeight_flip objects relation

end JanusFormal.ProgramM

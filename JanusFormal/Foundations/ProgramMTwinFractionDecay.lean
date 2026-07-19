import JanusFormal.Foundations.ProgramMInfiniteLayerNoGo

/-!
# MF-MAN-019: vanishing macroscopic relational-twin classes
-/

namespace JanusFormal.ProgramM

def RelationalTwin {α : Type*} (relation : α → α → Prop) (x y : α) : Prop :=
  (∀ z, relation x z ↔ relation y z) ∧
  (∀ z, relation z x ↔ relation z y)

theorem relationalTwin_orientation_invariant {α : Type*}
    (relation : α → α → Prop) (x y : α) :
    RelationalTwin (flip relation) x y ↔ RelationalTwin relation x y := by
  simp only [RelationalTwin, flip]
  constructor
  · rintro ⟨hpast, hfuture⟩
    exact ⟨hfuture, hpast⟩
  · rintro ⟨hfuture, hpast⟩
    exact ⟨hpast, hfuture⟩

def TwinFractionVanishes (fraction : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ threshold, ∀ size, threshold ≤ size → fraction size < ε

theorem positive_lower_bound_blocks_twin_fraction_decay
    (fraction : ℕ → ℝ) (lower : ℝ) (hlower : 0 < lower)
    (hboundedBelow : ∀ size, lower ≤ fraction size) :
    ¬ TwinFractionVanishes fraction := by
  intro hvis
  obtain ⟨threshold, hthreshold⟩ := hvis lower hlower
  exact (not_lt_of_ge (hboundedBelow threshold)) (hthreshold threshold le_rfl)

end JanusFormal.ProgramM


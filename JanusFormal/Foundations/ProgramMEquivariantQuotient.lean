import Mathlib.Data.Quot

/-! # MF-INV-003: descent of involutions through equivariant quotients -/

namespace Janus.ProgramM

variable {α : Type*}

def RespectsSetoid (r : Setoid α) (σ : α → α) : Prop :=
  ∀ ⦃x y⦄, r x y → r (σ x) (σ y)

def descendedMap (r : Setoid α) (σ : α → α)
    (hrespect : RespectsSetoid r σ) : Quotient r → Quotient r :=
  Quotient.map σ hrespect

@[simp]
theorem descendedMap_mk (r : Setoid α) (σ : α → α)
    (hrespect : RespectsSetoid r σ) (x : α) :
    descendedMap r σ hrespect ⟦x⟧ = ⟦σ x⟧ := rfl

theorem descendedMap_involutive (r : Setoid α) (σ : α → α)
    (hrespect : RespectsSetoid r σ) (hσ : Function.Involutive σ) :
    Function.Involutive (descendedMap r σ hrespect) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  simp [descendedMap, hσ x]

end Janus.ProgramM

import JanusFormal.Foundations.ProgramMEnsembleEmergence

/-!
# MF-ENS-002: exact obstruction for the first non-manifold competitor

The executable audit compares the Minkowski product-order law with this
exchangeable two-level law.  Here we prove the exact reason the latter is
rejected: it contains no strict chain of three elements.
-/

namespace JanusFormal.ProgramM

def twoLevelRel {n : ℕ} (upper : Fin n → Prop) (x y : Fin n) : Prop :=
  x = y ∨ (¬ upper x ∧ upper y)

theorem twoLevelRel_refl {n : ℕ} (upper : Fin n → Prop) (x : Fin n) :
    twoLevelRel upper x x :=
  Or.inl rfl

theorem twoLevelRel_antisymm {n : ℕ} (upper : Fin n → Prop) {x y : Fin n}
    (hxy : twoLevelRel upper x y) (hyx : twoLevelRel upper y x) : x = y := by
  rcases hxy with h | ⟨hx, hy⟩
  · exact h
  rcases hyx with h | ⟨hy', _⟩
  · exact h.symm
  exact False.elim (hy' hy)

theorem twoLevelRel_trans {n : ℕ} (upper : Fin n → Prop) {x y z : Fin n}
    (hxy : twoLevelRel upper x y) (hyz : twoLevelRel upper y z) :
    twoLevelRel upper x z := by
  rcases hxy with rfl | ⟨hx, hy⟩
  · exact hyz
  rcases hyz with rfl | ⟨hy', hz⟩
  · exact Or.inr ⟨hx, hy⟩
  exact False.elim (hy' hy)

def twoLevelPoset {n : ℕ} (upper : Fin n → Prop) : FinitePoset n where
  rel := twoLevelRel upper
  refl := twoLevelRel_refl upper
  antisymm := twoLevelRel_antisymm upper
  trans := twoLevelRel_trans upper

theorem twoLevelRel_no_strict_three_chain {n : ℕ} (upper : Fin n → Prop)
    {x y z : Fin n} (hxy : twoLevelRel upper x y) (hyz : twoLevelRel upper y z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) : False := by
  rcases hxy with h | ⟨_, hy⟩
  · exact hxy_ne h
  rcases hyz with h | ⟨hy', _⟩
  · exact hyz_ne h
  exact hy' hy

end JanusFormal.ProgramM


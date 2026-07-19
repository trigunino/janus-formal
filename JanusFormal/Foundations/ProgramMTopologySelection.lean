import JanusFormal.Foundations.ProgramMTopNoGo

/-!
# MF-SEL-001: when orientation stops mattering

This file characterizes exactly when the upper-set and lower-set Alexandrov
topologies of a preorder coincide.
-/

namespace JanusFormal.ProgramM

open Set Topology

universe u v

/-- Upper and lower Alexandrov conventions coincide exactly when every
comparison in the preorder is reversible. -/
theorem upperSet_eq_lowerSet_iff_symmetric (α : Type u) [Preorder α] :
    Topology.upperSet α = Topology.lowerSet α ↔
      ∀ ⦃a b : α⦄, a ≤ b → b ≤ a := by
  constructor
  · intro hTopology a b hab
    have hOpenUpper : @IsOpen α (Topology.upperSet α) (Ici b) := by
      show IsUpperSet (Ici b)
      exact isUpperSet_Ici b
    have hOpenLower : @IsOpen α (Topology.lowerSet α) (Ici b) := hTopology ▸ hOpenUpper
    have hLower : IsLowerSet (Ici b) := hOpenLower
    exact hLower hab (mem_Ici.mpr (le_refl b))
  · intro hSymm
    ext s
    change IsUpperSet s ↔ IsLowerSet s
    constructor
    · intro hUpper a b hab ha
      exact hUpper (hSymm hab) ha
    · intro hLower a b hab ha
      exact hLower (hSymm hab) ha

/-- MF-SEL-001 specialized to the topology reconstructed from a Program M
relation. It records the precise additional condition needed to remove the
upper/lower orientation convention. -/
theorem reconstructed_orientation_independent_iff
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel) :
    alexandrovTopology S q = alexandrovLowerTopology S q ↔
      ∀ ⦃x y : Obj⦄, reachability S q x y → reachability S q y x := by
  letI : Preorder Obj := reachabilityPreorder S q
  exact upperSet_eq_lowerSet_iff_symmetric Obj

end JanusFormal.ProgramM

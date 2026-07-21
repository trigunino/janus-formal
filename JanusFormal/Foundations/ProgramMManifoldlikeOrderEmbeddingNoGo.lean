import JanusFormal.Foundations.ProgramMCausalSetKinematics

/-!
# MF-MAN-000: order-embedding alone is not manifold-likeness

Every partial order embeds into its powerset by principal pasts. Hence the bare
existence of an order embedding into some ordered target is vacuous as a
manifold-likeness criterion.
-/

namespace JanusFormal.ProgramM

open Set

universe u v

/-- The principal-past representation of an arbitrary partial order. -/
def principalPastOrderEmbedding (α : Type u) [PartialOrder α] : α ↪o Set α where
  toFun a := Iic a
  inj' := by
    intro a b h
    change Iic a = Iic b at h
    apply le_antisymm
    · have : a ∈ Iic b := by
        rw [← h]
        exact le_rfl
      exact this
    · have : b ∈ Iic a := by
        rw [h]
        exact le_rfl
      exact this
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      exact h (show a ∈ Iic a from le_rfl)
    · intro hab x hxa
      exact hxa.trans hab

/-- Every Program M causal skeleton admits an exact order embedding into a
powerset, independently of geometry, dimension or manifold-likeness. -/
def causalSkeletonPrincipalPastEmbedding
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel) :
    CausalSkeleton S q ↪o Set (CausalSkeleton S q) :=
  principalPastOrderEmbedding (CausalSkeleton S q)

theorem causalSkeleton_principalPast_preserves_and_reflects_order
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (a b : CausalSkeleton S q) :
    causalSkeletonPrincipalPastEmbedding S q a ⊆
        causalSkeletonPrincipalPastEmbedding S q b ↔ a ≤ b :=
  (causalSkeletonPrincipalPastEmbedding S q).le_iff_le

end JanusFormal.ProgramM

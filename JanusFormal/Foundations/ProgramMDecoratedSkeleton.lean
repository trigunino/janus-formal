import JanusFormal.Foundations.ProgramMCausalSkeleton

/-!
# MF-DEC-001: lossless decoration of the oriented skeleton

The bare quotient is supplemented by its fibers and the original relation
between fiber elements. No metric or geometry is introduced.
-/

namespace JanusFormal.ProgramM

universe u v

/-- Primitive objects belonging to one mutual-reachability class. -/
def SkeletonFiber {Obj : Type u} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (q : Rel) (c : CausalSkeleton S q) :=
  {x : Obj // causalClass S q x = c}

/-- Every primitive object is exactly an element of one skeleton fiber. -/
def causalFiberDecompositionEquiv
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel) :
    Obj ≃ Σ c : CausalSkeleton S q, SkeletonFiber S q c where
  toFun x := ⟨causalClass S q x, ⟨x, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨c, x, hx⟩
    dsimp
    subst c
    rfl

/-- The original selected relation, expressed between decorated fibers. -/
def decoratedRelation
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel) :
    (Σ c : CausalSkeleton S q, SkeletonFiber S q c) →
      (Σ c : CausalSkeleton S q, SkeletonFiber S q c) → Prop :=
  fun x y ↦ S.holds q x.2.1 y.2.1

/-- The fiber decomposition loses none of the selected primitive relation. -/
theorem causalFiberDecomposition_preserves_relation
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Obj) :
    decoratedRelation S q (causalFiberDecompositionEquiv S q x)
        (causalFiberDecompositionEquiv S q y) ↔ S.holds q x y :=
  Iff.rfl

def IsInternalDecoratedEdge
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Σ c : CausalSkeleton S q, SkeletonFiber S q c) : Prop :=
  decoratedRelation S q x y ∧ x.1 = y.1

def IsBridgeDecoratedEdge
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Σ c : CausalSkeleton S q, SkeletonFiber S q c) : Prop :=
  decoratedRelation S q x y ∧ x.1 ≠ y.1

/-- Every primitive edge is uniquely classified as internal or inter-class. -/
theorem decoratedEdge_internal_or_bridge
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Σ c : CausalSkeleton S q, SkeletonFiber S q c) :
    decoratedRelation S q x y ↔
      IsInternalDecoratedEdge S q x y ∨ IsBridgeDecoratedEdge S q x y := by
  unfold IsInternalDecoratedEdge IsBridgeDecoratedEdge
  constructor
  · intro h
    exact (eq_or_ne x.1 y.1).imp (And.intro h) (And.intro h)
  · rintro (h | h) <;> exact h.1

theorem internal_bridge_disjoint
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Σ c : CausalSkeleton S q, SkeletonFiber S q c) :
    ¬ (IsInternalDecoratedEdge S q x y ∧ IsBridgeDecoratedEdge S q x y) := by
  rintro ⟨⟨_, hEq⟩, ⟨_, hNe⟩⟩
  exact hNe hEq

/-- Every bridge edge points strictly forward in the quotient order. -/
theorem bridgeEdge_strict_skeleton_order
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Σ c : CausalSkeleton S q, SkeletonFiber S q c)
    (h : IsBridgeDecoratedEdge S q x y) : x.1 < y.1 := by
  rw [lt_iff_le_not_ge]
  constructor
  · rw [← x.2.2, ← y.2.2, causalClass_le_iff_reachability]
    exact Relation.ReflTransGen.single h.1
  · intro hReverse
    exact h.2 (le_antisymm
      (by
        rw [← x.2.2, ← y.2.2, causalClass_le_iff_reachability]
        exact Relation.ReflTransGen.single h.1)
      hReverse)

end JanusFormal.ProgramM

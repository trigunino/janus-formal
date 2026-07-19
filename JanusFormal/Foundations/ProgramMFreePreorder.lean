import JanusFormal.Foundations.ProgramMDescentReachability

/-!
# MF-FREE-001: reachability is the free preorder on a primitive relation
-/

namespace JanusFormal.ProgramM

universe u v w

/-- Every primitive step belongs to generated reachability. -/
theorem primitive_le_reachability
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel)
    (q : Rel) {x y : Obj} (h : S.holds q x y) :
    reachability S q x y :=
  Relation.ReflTransGen.single h

/-- Minimality: every reflexive-transitive relation containing the primitive
steps also contains generated reachability. -/
theorem reachability_minimal
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (R : Obj → Obj → Prop)
    (hRefl : ∀ x, R x x)
    (hTrans : ∀ {x y z}, R x y → R y z → R x z)
    (hContains : ∀ {x y}, S.holds q x y → R x y)
    {x y : Obj} (hReach : reachability S q x y) :
    R x y := by
  induction hReach with
  | refl => exact hRefl _
  | tail hxy hyz ih => exact hTrans ih (hContains hyz)

/-- Universal mapping property into any preorder: checking a map only on
primitive steps is equivalent to checking it on all generated reachability. -/
theorem map_reachability_iff_map_primitive
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    {Target : Type w} [Preorder Target] (f : Obj → Target) :
    (∀ ⦃x y⦄, reachability S q x y → f x ≤ f y) ↔
      (∀ ⦃x y⦄, S.holds q x y → f x ≤ f y) := by
  constructor
  · intro h x y hxy
    exact h (primitive_le_reachability S q hxy)
  · intro h x y hxy
    exact reachability_minimal S q (fun a b ↦ f a ≤ f b)
      (fun _ ↦ le_refl _) (fun hab hbc ↦ hab.trans hbc)
      (fun {_ _} hab ↦ h hab) hxy

/-- Under primitive descent, the free preorder is equivalently generated from
the union of all locally witnessed steps. -/
theorem free_preorder_from_local_witnesses
    {ι : Type w} {Obj : Type u} {Rel : Type v}
    {global : RelationalSystem Obj Rel} (atlas : RelationalAtlas ι global)
    (hDescent : PrimitiveDescent atlas) (q : Rel) (x y : Obj) :
    reachability global q x y ↔
      Relation.ReflTransGen (HasLocalWitness atlas q) x y :=
  reachability_iff_local_witness_chain atlas hDescent q x y

end JanusFormal.ProgramM

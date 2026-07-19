import JanusFormal.Foundations.ProgramMTopologySelection
import Mathlib.Order.Antisymmetrization

/-!
# MF-CAUS-000: the oriented reachability skeleton

This is an order-theoretic construction. It is not yet physical causality.
-/

namespace JanusFormal.ProgramM

open Relation

universe u v

/-- Mutual-reachability classes, ordered by reachability between classes. -/
@[reducible] def CausalSkeleton {Obj : Type u} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (q : Rel) : Type u :=
  letI := reachabilityPreorder S q
  Antisymmetrization Obj (· ≤ ·)

instance causalSkeletonPartialOrder {Obj : Type u} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (q : Rel) : PartialOrder (CausalSkeleton S q) := by
  letI := reachabilityPreorder S q
  change PartialOrder (Antisymmetrization Obj (· ≤ ·))
  infer_instance

/-- Send a primitive object to its mutual-reachability class. -/
def causalClass {Obj : Type u} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (q : Rel) (x : Obj) : CausalSkeleton S q := by
  letI := reachabilityPreorder S q
  exact toAntisymmetrization (· ≤ ·) x

/-- The quotient identifies exactly the mutually reachable objects. -/
theorem causalClass_eq_iff_mutual_reachability
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Obj) :
    causalClass S q x = causalClass S q y ↔
      reachability S q x y ∧ reachability S q y x := by
  letI := reachabilityPreorder S q
  change toAntisymmetrization (· ≤ ·) x = toAntisymmetrization (· ≤ ·) y ↔ x ≤ y ∧ y ≤ x
  exact Quotient.eq''

/-- The quotient order preserves all reachability information between
mutual-reachability classes. -/
theorem causalClass_le_iff_reachability
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Obj) :
    causalClass S q x ≤ causalClass S q y ↔ reachability S q x y := by
  letI := reachabilityPreorder S q
  exact toAntisymmetrization_le_toAntisymmetrization_iff

/-- Strict order in the skeleton is precisely irreversible reachability. -/
theorem causalClass_lt_iff_irreversible_reachability
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (x y : Obj) :
    causalClass S q x < causalClass S q y ↔
      reachability S q x y ∧ ¬ reachability S q y x := by
  rw [lt_iff_le_not_ge, causalClass_le_iff_reachability,
    causalClass_le_iff_reachability]

end JanusFormal.ProgramM

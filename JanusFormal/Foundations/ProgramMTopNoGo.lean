import JanusFormal.Foundations.ProgramMTop001

/-!
# MF-NOGO-001/002: topology reconstruction is not unique

The witnesses are deliberately finite and contain no Janus-specific data.
-/

namespace JanusFormal.ProgramM

open Relation Set Topology

def emptyBoolSystem : RelationalSystem Bool Unit where
  holds := fun _ _ _ ↦ False

def loopBoolSystem : RelationalSystem Bool Unit where
  holds := fun _ x y ↦ x = y

theorem emptyBool_reachability_iff {x y : Bool} :
    reachability emptyBoolSystem () x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hFalse _ => exact False.elim hFalse
  · rintro rfl
    exact ReflTransGen.refl

theorem loopBool_reachability_iff {x y : Bool} :
    reachability loopBoolSystem () x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hyz ih => exact ih.trans hyz
  · rintro rfl
    exact ReflTransGen.refl

/-- MF-NOGO-001: retaining or deleting primitive self-loops changes the
relational system but not its reconstructed Alexandrov topology. -/
theorem different_relations_same_alexandrovTopology :
    alexandrovTopology emptyBoolSystem () =
      alexandrovTopology loopBoolSystem () := by
  have hp : reachabilityPreorder emptyBoolSystem () =
      reachabilityPreorder loopBoolSystem () := by
    apply Preorder.ext
    intro x y
    exact emptyBool_reachability_iff.trans loopBool_reachability_iff.symm
  change @Topology.upperSet Bool (reachabilityPreorder emptyBoolSystem ()) =
    @Topology.upperSet Bool (reachabilityPreorder loopBoolSystem ())
  rw [hp]

theorem empty_loop_not_isomorphic :
    ¬ Nonempty (RelationalSystemIso emptyBoolSystem loopBoolSystem) := by
  rintro ⟨e⟩
  have h := e.holds_iff () false false
  simp [emptyBoolSystem, loopBoolSystem] at h

def arrowBoolSystem : RelationalSystem Bool Unit where
  holds := fun _ x y ↦ x = false ∧ y = true

@[reducible] def alexandrovLowerTopology {Obj Rel : Type*}
    (S : RelationalSystem Obj Rel) (q : Rel) : TopologicalSpace Obj := by
  letI := reachabilityPreorder S q
  exact lowerSet Obj

theorem false_reaches_true : reachability arrowBoolSystem () false true :=
  ReflTransGen.single ⟨rfl, rfl⟩

theorem true_reachability_iff {y : Bool} :
    reachability arrowBoolSystem () true y ↔ y = true := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hyz ih =>
        rcases hyz with ⟨rfl, rfl⟩
        simp at ih
  · rintro rfl
    exact ReflTransGen.refl

/-- MF-NOGO-002: the same generated preorder supports distinct, equally
standard upper-set and lower-set Alexandrov topology conventions. -/
theorem upper_lower_topologies_differ :
    alexandrovTopology arrowBoolSystem () ≠
      alexandrovLowerTopology arrowBoolSystem () := by
  letI : Preorder Bool := reachabilityPreorder arrowBoolSystem ()
  change Topology.upperSet Bool ≠ Topology.lowerSet Bool
  intro hEq
  have hUpper : @IsOpen Bool (Topology.upperSet Bool) {true} := by
    show @IsUpperSet Bool (reachabilityPreorder arrowBoolSystem ()).toLE {true}
    intro a b hab ha
    simp only [mem_singleton_iff] at ha ⊢
    subst a
    exact true_reachability_iff.mp hab
  have hLower : @IsOpen Bool (Topology.lowerSet Bool) {true} := hEq ▸ hUpper
  have hLowerSet : @IsLowerSet Bool (reachabilityPreorder arrowBoolSystem ()).toLE {true} := hLower
  have := hLowerSet false_reaches_true (by simp)
  simp at this

end JanusFormal.ProgramM

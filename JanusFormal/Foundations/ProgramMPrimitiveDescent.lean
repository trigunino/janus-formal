import JanusFormal.Foundations.ProgramMConfigurationInterfaceGluing

/-!
# MF-DESC-001: primitive descent versus generated reachability

Primitive relations may satisfy a local-witness descent condition.  Global
reachability is reconstructed afterwards and need not itself have a local
witness in one patch.
-/

namespace JanusFormal.ProgramM

universe u v w

/-- A family of induced relational patches inside one global configuration. -/
structure RelationalAtlas
    (ι : Type w) {Obj : Type u} {Rel : Type v}
    (global : RelationalSystem Obj Rel) where
  PatchObj : ι → Type u
  patch : (i : ι) → RelationalSystem (PatchObj i) Rel
  embedding : (i : ι) → RelationalEmbedding (patch i) global

/-- A relation has a local witness when both endpoints and the relation occur
inside one patch. -/
def HasLocalWitness
    {ι : Type w} {Obj : Type u} {Rel : Type v}
    {global : RelationalSystem Obj Rel} (atlas : RelationalAtlas ι global)
    (q : Rel) (x y : Obj) : Prop :=
  ∃ (i : ι) (a b : atlas.PatchObj i),
    (atlas.embedding i).objEmbedding a = x ∧
    (atlas.embedding i).objEmbedding b = y ∧
    (atlas.patch i).holds q a b

/-- Primitive descent: the global primitive relation is exactly locally
witnessed relation data. -/
def PrimitiveDescent
    {ι : Type w} {Obj : Type u} {Rel : Type v}
    {global : RelationalSystem Obj Rel} (atlas : RelationalAtlas ι global) : Prop :=
  ∀ q x y, global.holds q x y ↔ HasLocalWitness atlas q x y

theorem primitiveDescent_holds_iff
    {ι : Type w} {Obj : Type u} {Rel : Type v}
    {global : RelationalSystem Obj Rel} (atlas : RelationalAtlas ι global)
    (h : PrimitiveDescent atlas) (q : Rel) (x y : Obj) :
    global.holds q x y ↔ HasLocalWitness atlas q x y :=
  h q x y

/-- A common local-witness predicate determines at most one primitive global
relation on fixed object and relation carriers. -/
theorem primitive_global_unique
    {Obj : Type u} {Rel : Type v}
    (left right : RelationalSystem Obj Rel) (witness : Rel → Obj → Obj → Prop)
    (hLeft : ∀ q x y, left.holds q x y ↔ witness q x y)
    (hRight : ∀ q x y, right.holds q x y ↔ witness q x y) :
    left = right := by
  cases left with
  | mk leftHolds =>
    cases right with
    | mk rightHolds =>
      congr
      funext q x y
      apply propext
      exact (hLeft q x y).trans (hRight q x y).symm

def threePointChainSystem : RelationalSystem (Fin 3) Unit where
  holds _ x y := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2)

/-- Reachability across two primitive local steps creates a global comparison
which is not itself a primitive relation. -/
theorem reachability_can_cross_patches :
    reachability threePointChainSystem () 0 2 ∧
      ¬ threePointChainSystem.holds () 0 2 := by
  constructor
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (Or.inl ⟨rfl, rfl⟩))
      (Relation.ReflTransGen.single (Or.inr ⟨rfl, rfl⟩))
  · simp [threePointChainSystem]

end JanusFormal.ProgramM

import JanusFormal.Foundations.ProgramMConfigurationComposition
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# MF-GLUE-001: free gluing along a relational interface

The object carrier is Mathlib's pushout of the interface embeddings.  The
relation is the union of relations inherited from the two pieces.
-/

namespace JanusFormal.ProgramM

open CategoryTheory
open CategoryTheory.Limits.Types

universe u v

/-- An induced copy of one relational configuration inside another. -/
structure RelationalEmbedding
    {Obj Obj' : Type u} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (T : RelationalSystem Obj' Rel) where
  objEmbedding : Obj ↪ Obj'
  holds_iff : ∀ q x y,
    T.holds q (objEmbedding x) (objEmbedding y) ↔ S.holds q x y

def RelationalEmbedding.objHom
    {Obj Obj' : Type u} {Rel : Type v}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel}
    (e : RelationalEmbedding S T) : Obj ⟶ Obj' :=
  ↾e.objEmbedding

/-- Object carrier obtained by identifying the two copies of the interface. -/
abbrev RelationalPushoutObj
    {IObj LObj RObj : Type u} {Rel : Type v}
    {I : RelationalSystem IObj Rel} {L : RelationalSystem LObj Rel}
    {R : RelationalSystem RObj Rel}
    (left : RelationalEmbedding I L) (right : RelationalEmbedding I R) : Type u :=
  Pushout left.objHom right.objHom

/-- Free relational gluing: retain relations witnessed inside either piece. -/
def relationalInterfaceGluing
    {IObj LObj RObj : Type u} {Rel : Type v}
    {I : RelationalSystem IObj Rel} {L : RelationalSystem LObj Rel}
    {R : RelationalSystem RObj Rel}
    (left : RelationalEmbedding I L) (right : RelationalEmbedding I R) :
    RelationalSystem (RelationalPushoutObj left right) Rel where
  holds q p s :=
    (∃ x y : LObj,
      Pushout.inl left.objHom right.objHom x = p ∧
      Pushout.inl left.objHom right.objHom y = s ∧ L.holds q x y) ∨
    (∃ x y : RObj,
      Pushout.inr left.objHom right.objHom x = p ∧
      Pushout.inr left.objHom right.objHom y = s ∧ R.holds q x y)

theorem relationalInterfaceGluing_inl
    {IObj LObj RObj : Type u} {Rel : Type v}
    {I : RelationalSystem IObj Rel} {L : RelationalSystem LObj Rel}
    {R : RelationalSystem RObj Rel}
    (left : RelationalEmbedding I L) (right : RelationalEmbedding I R)
    {q : Rel} {x y : LObj} (h : L.holds q x y) :
    (relationalInterfaceGluing left right).holds q
      (Pushout.inl left.objHom right.objHom x)
      (Pushout.inl left.objHom right.objHom y) := by
  exact Or.inl ⟨x, y, rfl, rfl, h⟩

theorem relationalInterfaceGluing_inr
    {IObj LObj RObj : Type u} {Rel : Type v}
    {I : RelationalSystem IObj Rel} {L : RelationalSystem LObj Rel}
    {R : RelationalSystem RObj Rel}
    (left : RelationalEmbedding I L) (right : RelationalEmbedding I R)
    {q : Rel} {x y : RObj} (h : R.holds q x y) :
    (relationalInterfaceGluing left right).holds q
      (Pushout.inr left.objHom right.objHom x)
      (Pushout.inr left.objHom right.objHom y) := by
  exact Or.inr ⟨x, y, rfl, rfl, h⟩

def loopUnitSystem : RelationalSystem Unit Unit where
  holds _ _ _ := True

def emptyUnitSystem : RelationalSystem Unit Unit where
  holds _ _ _ := False

/-- An interface cannot be embedded as an induced subsystem when the pieces
disagree on its internal relation. -/
theorem incompatible_interface_has_no_embedding :
    ¬ Nonempty (RelationalEmbedding loopUnitSystem emptyUnitSystem) := by
  rintro ⟨e⟩
  have h := e.holds_iff () () ()
  simp [loopUnitSystem, emptyUnitSystem] at h

end JanusFormal.ProgramM

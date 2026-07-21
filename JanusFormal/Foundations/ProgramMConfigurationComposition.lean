import JanusFormal.Foundations.ProgramMConfigurationGroupoid
import Mathlib.Logic.Equiv.Sum

/-!
# MF-COMP-002: composition of relational configurations

Disjoint sum is canonical for configurations with a common relation signature.
Cross-component relations require additional interface data.
-/

namespace JanusFormal.ProgramM

universe u u' u'' v

/-- Canonical composition with no cross-component relations. -/
def relationalDisjointSum
    {Obj : Type u} {Obj' : Type u'} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (T : RelationalSystem Obj' Rel) :
    RelationalSystem (Obj ⊕ Obj') Rel where
  holds q x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => S.holds q a b
    | Sum.inr a, Sum.inr b => T.holds q a b
    | _, _ => False

/-- Empty configuration for a fixed relation signature. -/
def emptyRelationalSystem (Rel : Type v) : RelationalSystem Empty Rel where
  holds _ x _ := nomatch x

/-- Disjoint composition is associative up to exact relational isomorphism. -/
def relationalDisjointSumAssoc
    {Obj : Type u} {Obj' : Type u'} {Obj'' : Type u''} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (T : RelationalSystem Obj' Rel)
    (U : RelationalSystem Obj'' Rel) :
    RelationalSystemIso
      (relationalDisjointSum (relationalDisjointSum S T) U)
      (relationalDisjointSum S (relationalDisjointSum T U)) where
  objEquiv := Equiv.sumAssoc Obj Obj' Obj''
  relEquiv := Equiv.refl Rel
  holds_iff := by
    intro q x y
    rcases x with (a | b) | c <;> rcases y with (a' | b') | c' <;>
      simp [relationalDisjointSum]

/-- The order of disconnected components is irrelevant up to isomorphism. -/
def relationalDisjointSumComm
    {Obj : Type u} {Obj' : Type u'} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (T : RelationalSystem Obj' Rel) :
    RelationalSystemIso (relationalDisjointSum S T) (relationalDisjointSum T S) where
  objEquiv := Equiv.sumComm Obj Obj'
  relEquiv := Equiv.refl Rel
  holds_iff := by
    intro q x y
    rcases x with a | b <;> rcases y with a' | b' <;> simp [relationalDisjointSum]

def relationalDisjointSumLeftUnit
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) :
    RelationalSystemIso (relationalDisjointSum (emptyRelationalSystem Rel) S) S where
  objEquiv := Equiv.emptySum Empty Obj
  relEquiv := Equiv.refl Rel
  holds_iff := by
    intro q x y
    rcases x with x | x <;> rcases y with y | y
    · exact Empty.elim x
    · exact Empty.elim x
    · exact Empty.elim y
    · rfl

def relationalDisjointSumRightUnit
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) :
    RelationalSystemIso (relationalDisjointSum S (emptyRelationalSystem Rel)) S where
  objEquiv := Equiv.sumEmpty Obj Empty
  relEquiv := Equiv.refl Rel
  holds_iff := by
    intro q x y
    rcases x with x | x <;> rcases y with y | y
    · rfl
    · exact Empty.elim y
    · exact Empty.elim x
    · exact Empty.elim x

/-- Extra data needed to add directed relations between two components. -/
structure CrossRelationData
    (Obj : Type u) (Obj' : Type u') (Rel : Type v) where
  leftToRight : Rel → Obj → Obj' → Prop
  rightToLeft : Rel → Obj' → Obj → Prop

/-- General composition after cross-component data have been supplied. -/
def relationalSumWithCross
    {Obj : Type u} {Obj' : Type u'} {Rel : Type v}
    (S : RelationalSystem Obj Rel) (T : RelationalSystem Obj' Rel)
    (cross : CrossRelationData Obj Obj' Rel) : RelationalSystem (Obj ⊕ Obj') Rel where
  holds q x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => S.holds q a b
    | Sum.inr a, Sum.inr b => T.holds q a b
    | Sum.inl a, Sum.inr b => cross.leftToRight q a b
    | Sum.inr a, Sum.inl b => cross.rightToLeft q a b

def emptyCrossRelationData (Obj : Type u) (Obj' : Type u') (Rel : Type v) :
    CrossRelationData Obj Obj' Rel where
  leftToRight _ _ _ := False
  rightToLeft _ _ _ := False

def fullCrossRelationData (Obj : Type u) (Obj' : Type u') (Rel : Type v) :
    CrossRelationData Obj Obj' Rel where
  leftToRight _ _ _ := True
  rightToLeft _ _ _ := True

/-- The two pieces alone do not determine their cross relations. -/
theorem cross_relations_are_extra_data
    (S T : RelationalSystem Unit Unit) :
    (relationalSumWithCross S T (emptyCrossRelationData Unit Unit Unit)).holds
        () (Sum.inl ()) (Sum.inr ()) = False ∧
      (relationalSumWithCross S T (fullCrossRelationData Unit Unit Unit)).holds
        () (Sum.inl ()) (Sum.inr ()) = True := by
  exact ⟨rfl, rfl⟩

end JanusFormal.ProgramM

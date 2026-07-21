import JanusFormal.Foundations.ProgramMTop001

/-!
# MF-CONF-001: the configuration groupoid of relational systems

Relational systems are configurations and simultaneous relation/object
relabelings are invertible arrows.  No topology, metric or physics is used.
-/

namespace JanusFormal.ProgramM

universe u v u' v' u'' v'' u''' v'''

namespace RelationalSystemIso

/-- Identity arrow of a relational configuration. -/
def refl {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) :
    RelationalSystemIso S S where
  objEquiv := Equiv.refl Obj
  relEquiv := Equiv.refl Rel
  holds_iff := by simp

/-- Every configuration arrow is invertible. -/
def symm {Obj : Type u} {Rel : Type v} {Obj' : Type u'} {Rel' : Type v'}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel'}
    (e : RelationalSystemIso S T) : RelationalSystemIso T S where
  objEquiv := e.objEquiv.symm
  relEquiv := e.relEquiv.symm
  holds_iff := by
    intro q x y
    simpa using (e.holds_iff (e.relEquiv.symm q) (e.objEquiv.symm x) (e.objEquiv.symm y)).symm

/-- Composition of exact relabelings. -/
def trans
    {Obj : Type u} {Rel : Type v}
    {Obj' : Type u'} {Rel' : Type v'}
    {Obj'' : Type u''} {Rel'' : Type v''}
    {S : RelationalSystem Obj Rel}
    {T : RelationalSystem Obj' Rel'}
    {U : RelationalSystem Obj'' Rel''}
    (e : RelationalSystemIso S T) (f : RelationalSystemIso T U) :
    RelationalSystemIso S U where
  objEquiv := e.objEquiv.trans f.objEquiv
  relEquiv := e.relEquiv.trans f.relEquiv
  holds_iff := by
    intro q x y
    exact (f.holds_iff (e.relEquiv q) (e.objEquiv x) (e.objEquiv y)).trans
      (e.holds_iff q x y)

@[ext]
theorem ext
    {Obj : Type u} {Rel : Type v} {Obj' : Type u'} {Rel' : Type v'}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel'}
    {e f : RelationalSystemIso S T}
    (hObj : e.objEquiv = f.objEquiv) (hRel : e.relEquiv = f.relEquiv) : e = f := by
  cases e
  cases f
  cases hObj
  cases hRel
  rfl

theorem refl_trans
    {Obj : Type u} {Rel : Type v} {Obj' : Type u'} {Rel' : Type v'}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel'}
    (e : RelationalSystemIso S T) : trans (refl S) e = e := by
  ext <;> simp [trans, refl]

theorem trans_refl
    {Obj : Type u} {Rel : Type v} {Obj' : Type u'} {Rel' : Type v'}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel'}
    (e : RelationalSystemIso S T) : trans e (refl T) = e := by
  ext <;> simp [trans, refl]

theorem trans_assoc
    {Obj : Type u} {Rel : Type v}
    {Obj' : Type u'} {Rel' : Type v'}
    {Obj'' : Type u''} {Rel'' : Type v''}
    {Obj''' : Type u'''} {Rel''' : Type v'''}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel'}
    {U : RelationalSystem Obj'' Rel''} {V : RelationalSystem Obj''' Rel'''}
    (e : RelationalSystemIso S T) (f : RelationalSystemIso T U)
    (g : RelationalSystemIso U V) :
    trans (trans e f) g = trans e (trans f g) := by
  ext <;> rfl

theorem trans_symm
    {Obj : Type u} {Rel : Type v} {Obj' : Type u'} {Rel' : Type v'}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel'}
    (e : RelationalSystemIso S T) : trans e (symm e) = refl S := by
  ext <;> simp [trans, symm, refl]

theorem symm_trans
    {Obj : Type u} {Rel : Type v} {Obj' : Type u'} {Rel' : Type v'}
    {S : RelationalSystem Obj Rel} {T : RelationalSystem Obj' Rel'}
    (e : RelationalSystemIso S T) : trans (symm e) e = refl T := by
  ext <;> simp [trans, symm, refl]

end RelationalSystemIso

end JanusFormal.ProgramM

import JanusFormal.Foundations.ProgramMObservableFactorization
import Mathlib.Order.Interval.Finset.Defs

/-!
# MF-CAUS-001: causal-set kinematics gate

The standard causal-set kinematical condition is a locally finite partial
order. Passing this gate does not by itself identify physical causality.
-/

namespace JanusFormal.ProgramM

open Set

universe u v

/-- Local finiteness stated without installing a computational interval
instance: every closed order interval is a finite set. -/
def IsLocallyFiniteKinematics (α : Type u) [PartialOrder α] : Prop :=
  ∀ a b : α, (Icc a b).Finite

/-- The Program M skeleton passes the standard causal-set kinematical gate
whenever the primitive object type is finite. -/
theorem finite_causalSkeleton_isLocallyFinite
    {Obj : Type u} {Rel : Type v} [Finite Obj]
    (S : RelationalSystem Obj Rel) (q : Rel) :
    IsLocallyFiniteKinematics (CausalSkeleton S q) := by
  letI : Finite (CausalSkeleton S q) := Finite.of_surjective (causalClass S q) (by
    intro c
    induction c using Antisymmetrization.ind with
    | _ x => exact ⟨x, rfl⟩)
  intro a b
  exact Set.toFinite (Icc a b)

/-- MF-NOGO-CAUS-001: local finiteness cannot discriminate any candidates in
an enumeration whose primitive carrier is already finite. -/
theorem finite_census_localFiniteness_filter_is_vacuous
    {Obj : Type u} {Rel : Type v} [Finite Obj]
    (candidate : RelationalSystem Obj Rel) (q : Rel) :
    IsLocallyFiniteKinematics (CausalSkeleton candidate q) :=
  finite_causalSkeleton_isLocallyFinite candidate q

/-- Strict skeleton order has no directed self-loop. This is order-theoretic
acyclicity, not yet a physical no-closed-timelike-curve theorem. -/
theorem causalSkeleton_strict_irreflexive
    {Obj : Type u} {Rel : Type v} (S : RelationalSystem Obj Rel) (q : Rel)
    (c : CausalSkeleton S q) : ¬ c < c :=
  lt_irrefl c

end JanusFormal.ProgramM

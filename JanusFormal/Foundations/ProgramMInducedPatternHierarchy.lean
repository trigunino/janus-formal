import JanusFormal.Foundations.ProgramMDecoratedLayerAdversary

/-!
# MF-PAT-001: induced finite-pattern hierarchy
-/

namespace JanusFormal.ProgramM

def embeddingComp {α β γ : Type*} (f : β ↪ γ) (g : α ↪ β) : α ↪ γ where
  toFun x := f (g x)
  inj' := f.injective.comp g.injective

theorem FinitePoset.induce_comp {j k n : ℕ} (P : FinitePoset n)
    (f : Fin k ↪ Fin n) (g : Fin j ↪ Fin k) :
    (P.induce f).induce g = P.induce (embeddingComp f g) := by
  rfl

theorem FinitePoset.induce_relabel {k n : ℕ} (P : FinitePoset n)
    (e : Equiv.Perm (Fin n)) (f : Fin k ↪ Fin n) :
    (P.relabel e).induce f = P.induce (embeddingComp e.symm.toEmbedding f) := by
  rfl

/-- Agreement at one finite rank is a finite diagnostic. -/
def AgreesAtPatternRank
    (left right : ExchangeableProjectiveOrderLaw) (rank : ℕ) : Prop :=
  left.law rank = right.law rank

/-- The full hierarchy is the observational equivalence appropriate to the
exchangeable projective law itself. -/
def PatternHierarchyEquivalent
    (left right : ExchangeableProjectiveOrderLaw) : Prop :=
  ∀ rank, AgreesAtPatternRank left right rank

theorem patternHierarchyEquivalent_refl
    (model : ExchangeableProjectiveOrderLaw) :
    PatternHierarchyEquivalent model model := by
  intro rank
  rfl

theorem patternHierarchyEquivalent_symm
    {left right : ExchangeableProjectiveOrderLaw}
    (h : PatternHierarchyEquivalent left right) :
    PatternHierarchyEquivalent right left := by
  intro rank
  exact (h rank).symm

theorem patternHierarchyEquivalent_trans
    {first second third : ExchangeableProjectiveOrderLaw}
    (h₁ : PatternHierarchyEquivalent first second)
    (h₂ : PatternHierarchyEquivalent second third) :
    PatternHierarchyEquivalent first third := by
  intro rank
  exact (h₁ rank).trans (h₂ rank)

/-- Rank one contains no order information: every one-object partial order is
the same.  Thus a fixed low rank cannot be promoted to universal identification. -/
theorem finitePoset_one_unique (P Q : FinitePoset 1) : P = Q := by
  cases P with
  | mk prel prefl pantisymm ptrans =>
    cases Q with
    | mk qrel qrefl qantisymm qtrans =>
      congr
      funext x y
      apply propext
      constructor <;> intro _
      · have hxy : x = y := Subsingleton.elim x y
        subst y
        exact qrefl x
      · have hxy : x = y := Subsingleton.elim x y
        subst y
        exact prefl x

end JanusFormal.ProgramM

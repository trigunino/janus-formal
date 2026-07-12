import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteJetEquivariance

set_option autoImplicit false

universe u v w x

/-- A deliberately light action interface.  Group laws are irrelevant for the
finite-jet classification lemma; only the compatible actions matter. -/
structure ActionData (Symmetry : Type u) (Space : Type v) where
  act : Symmetry → Space → Space

/-- Equivariance of a map between two action spaces. -/
def IsEquivariant
    {Symmetry : Type u}
    {Source : Type v}
    {Target : Type w}
    (sourceAction : ActionData Symmetry Source)
    (targetAction : ActionData Symmetry Target)
    (map : Source → Target) : Prop :=
  ∀ symmetry source,
    map (sourceAction.act symmetry source) =
      targetAction.act symmetry (map source)

/-- Naturality of an operator under the same symmetry. -/
def IsNaturalOperator
    {Symmetry : Type u}
    {Section : Type v}
    {Target : Type w}
    (sectionAction : ActionData Symmetry Section)
    (targetAction : ActionData Symmetry Target)
    (operator : Section → Target) : Prop :=
  ∀ symmetry section,
    operator (sectionAction.act symmetry section) =
      targetAction.act symmetry (operator section)

/-- Data of a finite-jet presentation. -/
structure FiniteJetPresentation
    (Symmetry : Type u)
    (Section : Type v)
    (Jet : Type w)
    (Target : Type x) where
  sectionAction : ActionData Symmetry Section
  jetAction : ActionData Symmetry Jet
  targetAction : ActionData Symmetry Target
  jet : Section → Jet
  jetEquivariant :
    ∀ symmetry section,
      jet (sectionAction.act symmetry section) =
        jetAction.act symmetry (jet section)
  jetSurjective : Function.Surjective jet
  operator : Section → Target
  evaluator : Jet → Target
  factorization :
    ∀ section,
      operator section = evaluator (jet section)

/-- The jet evaluator is unique whenever the jet map is surjective. -/
theorem evaluator_unique_of_surjective_jet
    {Symmetry : Type u}
    {Section : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry Section Jet Target)
    (otherEvaluator : Jet → Target)
    (hOtherFactorization :
      ∀ section,
        presentation.operator section =
          otherEvaluator (presentation.jet section)) :
    otherEvaluator = presentation.evaluator := by
  funext jetValue
  rcases presentation.jetSurjective jetValue with
    ⟨section, rfl⟩
  calc
    otherEvaluator (presentation.jet section) =
        presentation.operator section :=
      (hOtherFactorization section).symm
    _ = presentation.evaluator
        (presentation.jet section) :=
      presentation.factorization section

/-- If the evaluator is equivariant, the induced operator is natural. -/
theorem evaluator_equivariant_implies_operator_natural
    {Symmetry : Type u}
    {Section : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry Section Jet Target)
    (hEvaluator :
      IsEquivariant presentation.jetAction
        presentation.targetAction presentation.evaluator) :
    IsNaturalOperator presentation.sectionAction
      presentation.targetAction presentation.operator := by
  intro symmetry section
  calc
    presentation.operator
        (presentation.sectionAction.act symmetry section) =
      presentation.evaluator
        (presentation.jet
          (presentation.sectionAction.act symmetry section)) :=
      presentation.factorization _
    _ = presentation.evaluator
        (presentation.jetAction.act symmetry
          (presentation.jet section)) := by
      rw [presentation.jetEquivariant]
    _ = presentation.targetAction.act symmetry
        (presentation.evaluator
          (presentation.jet section)) :=
      hEvaluator symmetry (presentation.jet section)
    _ = presentation.targetAction.act symmetry
        (presentation.operator section) := by
      rw [presentation.factorization]

/-- If the factorized operator is natural and the jet map is surjective, the
jet evaluator must be equivariant. -/
theorem operator_natural_implies_evaluator_equivariant
    {Symmetry : Type u}
    {Section : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry Section Jet Target)
    (hOperator :
      IsNaturalOperator presentation.sectionAction
        presentation.targetAction presentation.operator) :
    IsEquivariant presentation.jetAction
      presentation.targetAction presentation.evaluator := by
  intro symmetry jetValue
  rcases presentation.jetSurjective jetValue with
    ⟨section, rfl⟩
  calc
    presentation.evaluator
        (presentation.jetAction.act symmetry
          (presentation.jet section)) =
      presentation.evaluator
        (presentation.jet
          (presentation.sectionAction.act symmetry section)) := by
      rw [presentation.jetEquivariant]
    _ = presentation.operator
        (presentation.sectionAction.act symmetry section) :=
      (presentation.factorization _).symm
    _ = presentation.targetAction.act symmetry
        (presentation.operator section) :=
      hOperator symmetry section
    _ = presentation.targetAction.act symmetry
        (presentation.evaluator
          (presentation.jet section)) := by
      rw [presentation.factorization]

/-- Exact finite-jet classification theorem: naturality of a factorized
operator is equivalent to equivariance of its unique jet evaluator. -/
theorem operator_natural_iff_evaluator_equivariant
    {Symmetry : Type u}
    {Section : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry Section Jet Target) :
    IsNaturalOperator presentation.sectionAction
        presentation.targetAction presentation.operator ↔
      IsEquivariant presentation.jetAction
        presentation.targetAction presentation.evaluator := by
  constructor
  · exact operator_natural_implies_evaluator_equivariant presentation
  · exact evaluator_equivariant_implies_operator_natural presentation

/-- A natural factorized operator has a unique equivariant evaluator. -/
theorem exists_unique_equivariant_evaluator
    {Symmetry : Type u}
    {Section : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry Section Jet Target)
    (hNatural :
      IsNaturalOperator presentation.sectionAction
        presentation.targetAction presentation.operator) :
    ∃! evaluator : Jet → Target,
      (∀ section,
        presentation.operator section =
          evaluator (presentation.jet section)) /\
      IsEquivariant presentation.jetAction
        presentation.targetAction evaluator := by
  refine ⟨presentation.evaluator, ?_, ?_⟩
  · exact ⟨presentation.factorization,
      operator_natural_implies_evaluator_equivariant
        presentation hNatural⟩
  · intro otherEvaluator hOther
    exact evaluator_unique_of_surjective_jet
      presentation otherEvaluator hOther.1

/--
This theorem is the exact algebraic heart of the jet-classification claim.
Peetre--Slovak is needed only to supply the finite-jet factorization; once that
factorization and jet surjectivity are available, equivariance and uniqueness
follow formally.
-/
structure FiniteJetPhysicalStatus where
  decoratedImmersionSymmetryConstructed : Prop
  sectionAndTargetActionsConstructed : Prop
  finiteJetBundleConstructed : Prop
  holonomicJetRealizationProved : Prop
  naturalityProved : Prop
  peetreSlovakFactorizationProved : Prop
  evaluatorEquivarianceDerived : Prop
  evaluatorUniquenessDerived : Prop


def finiteJetPhysicalClosure
    (s : FiniteJetPhysicalStatus) : Prop :=
  s.decoratedImmersionSymmetryConstructed /\
  s.sectionAndTargetActionsConstructed /\
  s.finiteJetBundleConstructed /\
  s.holonomicJetRealizationProved /\
  s.naturalityProved /\
  s.peetreSlovakFactorizationProved /\
  s.evaluatorEquivarianceDerived /\
  s.evaluatorUniquenessDerived

end P0EFTJanusFiniteJetEquivariance
end JanusFormal

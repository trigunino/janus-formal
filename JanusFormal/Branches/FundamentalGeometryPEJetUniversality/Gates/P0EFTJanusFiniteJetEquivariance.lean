import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteJetEquivariance

set_option autoImplicit false

universe u v w x

/-- A deliberately light action interface. Group laws are irrelevant for the
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
  ∀ symmetry sourceValue,
    map (sourceAction.act symmetry sourceValue) =
      targetAction.act symmetry (map sourceValue)

/-- Naturality of an operator under the same symmetry. -/
def IsNaturalOperator
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Target : Type w}
    (sectionAction : ActionData Symmetry SectionSpace)
    (targetAction : ActionData Symmetry Target)
    (operator : SectionSpace → Target) : Prop :=
  ∀ symmetry sectionValue,
    operator (sectionAction.act symmetry sectionValue) =
      targetAction.act symmetry (operator sectionValue)

/-- Data of a finite-jet presentation. -/
structure FiniteJetPresentation
    (Symmetry : Type u)
    (SectionSpace : Type v)
    (Jet : Type w)
    (Target : Type x) where
  sectionAction : ActionData Symmetry SectionSpace
  jetAction : ActionData Symmetry Jet
  targetAction : ActionData Symmetry Target
  jet : SectionSpace → Jet
  jetEquivariant :
    ∀ symmetry sectionValue,
      jet (sectionAction.act symmetry sectionValue) =
        jetAction.act symmetry (jet sectionValue)
  jetSurjective : Function.Surjective jet
  operator : SectionSpace → Target
  evaluator : Jet → Target
  factorization :
    ∀ sectionValue,
      operator sectionValue = evaluator (jet sectionValue)

/-- The jet evaluator is unique whenever the jet map is surjective. -/
theorem evaluator_unique_of_surjective_jet
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry SectionSpace Jet Target)
    (otherEvaluator : Jet → Target)
    (hOtherFactorization :
      ∀ sectionValue,
        presentation.operator sectionValue =
          otherEvaluator (presentation.jet sectionValue)) :
    otherEvaluator = presentation.evaluator := by
  funext jetValue
  rcases presentation.jetSurjective jetValue with
    ⟨sectionValue, rfl⟩
  calc
    otherEvaluator (presentation.jet sectionValue) =
        presentation.operator sectionValue :=
      (hOtherFactorization sectionValue).symm
    _ = presentation.evaluator
        (presentation.jet sectionValue) :=
      presentation.factorization sectionValue

/-- If the evaluator is equivariant, the induced operator is natural. -/
theorem evaluator_equivariant_implies_operator_natural
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry SectionSpace Jet Target)
    (hEvaluator :
      IsEquivariant presentation.jetAction
        presentation.targetAction presentation.evaluator) :
    IsNaturalOperator presentation.sectionAction
      presentation.targetAction presentation.operator := by
  intro symmetry sectionValue
  calc
    presentation.operator
        (presentation.sectionAction.act symmetry sectionValue) =
      presentation.evaluator
        (presentation.jet
          (presentation.sectionAction.act symmetry sectionValue)) :=
      presentation.factorization _
    _ = presentation.evaluator
        (presentation.jetAction.act symmetry
          (presentation.jet sectionValue)) := by
      rw [presentation.jetEquivariant]
    _ = presentation.targetAction.act symmetry
        (presentation.evaluator
          (presentation.jet sectionValue)) :=
      hEvaluator symmetry (presentation.jet sectionValue)
    _ = presentation.targetAction.act symmetry
        (presentation.operator sectionValue) := by
      rw [presentation.factorization]

/-- If the factorized operator is natural and the jet map is surjective, the
jet evaluator must be equivariant. -/
theorem operator_natural_implies_evaluator_equivariant
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry SectionSpace Jet Target)
    (hOperator :
      IsNaturalOperator presentation.sectionAction
        presentation.targetAction presentation.operator) :
    IsEquivariant presentation.jetAction
      presentation.targetAction presentation.evaluator := by
  intro symmetry jetValue
  rcases presentation.jetSurjective jetValue with
    ⟨sectionValue, rfl⟩
  calc
    presentation.evaluator
        (presentation.jetAction.act symmetry
          (presentation.jet sectionValue)) =
      presentation.evaluator
        (presentation.jet
          (presentation.sectionAction.act symmetry sectionValue)) := by
      rw [presentation.jetEquivariant]
    _ = presentation.operator
        (presentation.sectionAction.act symmetry sectionValue) :=
      (presentation.factorization _).symm
    _ = presentation.targetAction.act symmetry
        (presentation.operator sectionValue) :=
      hOperator symmetry sectionValue
    _ = presentation.targetAction.act symmetry
        (presentation.evaluator
          (presentation.jet sectionValue)) := by
      rw [presentation.factorization]

/-- Exact finite-jet classification theorem: naturality of a factorized
operator is equivalent to equivariance of its unique jet evaluator. -/
theorem operator_natural_iff_evaluator_equivariant
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry SectionSpace Jet Target) :
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
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (presentation :
      FiniteJetPresentation Symmetry SectionSpace Jet Target)
    (hNatural :
      IsNaturalOperator presentation.sectionAction
        presentation.targetAction presentation.operator) :
    ∃! evaluator : Jet → Target,
      (∀ sectionValue,
        presentation.operator sectionValue =
          evaluator (presentation.jet sectionValue)) /\
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

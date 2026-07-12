import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteJetEquivariance

namespace JanusFormal
namespace P0EFTJanusFiniteJetOperatorConstruction

set_option autoImplicit false

open P0EFTJanusFiniteJetEquivariance

universe u v w x

/-- Data from which a finite-order operator is constructed, rather than assumed. -/
structure FiniteJetConstruction
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
  evaluator : Jet → Target

/-- Operator induced by a finite-jet evaluator. -/
def inducedOperator
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : FiniteJetConstruction Symmetry SectionSpace Jet Target) :
    SectionSpace → Target :=
  fun sectionValue => data.evaluator (data.jet sectionValue)

/-- The induced operator factors through the declared jet map by definition. -/
@[simp] theorem induced_operator_factorization
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : FiniteJetConstruction Symmetry SectionSpace Jet Target)
    (sectionValue : SectionSpace) :
    inducedOperator data sectionValue =
      data.evaluator (data.jet sectionValue) := by
  rfl

/-- An equivariant evaluator produces a natural operator. -/
theorem equivariant_evaluator_induces_natural_operator
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : FiniteJetConstruction Symmetry SectionSpace Jet Target)
    (hEvaluator :
      IsEquivariant data.jetAction data.targetAction data.evaluator) :
    IsNaturalOperator data.sectionAction data.targetAction
      (inducedOperator data) := by
  intro symmetry sectionValue
  calc
    inducedOperator data
        (data.sectionAction.act symmetry sectionValue) =
      data.evaluator
        (data.jet
          (data.sectionAction.act symmetry sectionValue)) := rfl
    _ = data.evaluator
        (data.jetAction.act symmetry
          (data.jet sectionValue)) := by
      rw [data.jetEquivariant]
    _ = data.targetAction.act symmetry
        (data.evaluator (data.jet sectionValue)) :=
      hEvaluator symmetry (data.jet sectionValue)
    _ = data.targetAction.act symmetry
        (inducedOperator data sectionValue) := rfl

/-- Naturality of the induced operator forces evaluator equivariance when every jet is realizable. -/
theorem natural_induced_operator_forces_evaluator_equivariance
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : FiniteJetConstruction Symmetry SectionSpace Jet Target)
    (hOperator :
      IsNaturalOperator data.sectionAction data.targetAction
        (inducedOperator data)) :
    IsEquivariant data.jetAction data.targetAction data.evaluator := by
  intro symmetry jetValue
  rcases data.jetSurjective jetValue with ⟨sectionValue, rfl⟩
  calc
    data.evaluator
        (data.jetAction.act symmetry (data.jet sectionValue)) =
      data.evaluator
        (data.jet
          (data.sectionAction.act symmetry sectionValue)) := by
      rw [data.jetEquivariant]
    _ = inducedOperator data
        (data.sectionAction.act symmetry sectionValue) := rfl
    _ = data.targetAction.act symmetry
        (inducedOperator data sectionValue) :=
      hOperator symmetry sectionValue
    _ = data.targetAction.act symmetry
        (data.evaluator (data.jet sectionValue)) := rfl

/-- Constructive form of Lemma 2. -/
theorem induced_operator_natural_iff_evaluator_equivariant
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : FiniteJetConstruction Symmetry SectionSpace Jet Target) :
    IsNaturalOperator data.sectionAction data.targetAction
        (inducedOperator data) ↔
      IsEquivariant data.jetAction data.targetAction data.evaluator := by
  constructor
  · exact natural_induced_operator_forces_evaluator_equivariance data
  · exact equivariant_evaluator_induces_natural_operator data

/-- The evaluator of the induced operator is unique under jet surjectivity. -/
theorem induced_evaluator_unique
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : FiniteJetConstruction Symmetry SectionSpace Jet Target)
    (otherEvaluator : Jet → Target)
    (hFactorization :
      ∀ sectionValue,
        inducedOperator data sectionValue =
          otherEvaluator (data.jet sectionValue)) :
    otherEvaluator = data.evaluator := by
  funext jetValue
  rcases data.jetSurjective jetValue with ⟨sectionValue, rfl⟩
  calc
    otherEvaluator (data.jet sectionValue) =
        inducedOperator data sectionValue :=
      (hFactorization sectionValue).symm
    _ = data.evaluator (data.jet sectionValue) := rfl

/-- Exact constructive classification: an equivariant evaluator gives one unique natural factorized operator. -/
theorem exists_unique_natural_operator_from_equivariant_evaluator
    {Symmetry : Type u}
    {SectionSpace : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : FiniteJetConstruction Symmetry SectionSpace Jet Target)
    (hEvaluator :
      IsEquivariant data.jetAction data.targetAction data.evaluator) :
    ∃! operator : SectionSpace → Target,
      (∀ sectionValue,
        operator sectionValue = data.evaluator (data.jet sectionValue)) /\
      IsNaturalOperator data.sectionAction data.targetAction operator := by
  refine ⟨inducedOperator data, ?_, ?_⟩
  · exact ⟨induced_operator_factorization data,
      equivariant_evaluator_induces_natural_operator data hEvaluator⟩
  · intro otherOperator hOther
    funext sectionValue
    rw [hOther.1 sectionValue]
    rfl

end P0EFTJanusFiniteJetOperatorConstruction
end JanusFormal

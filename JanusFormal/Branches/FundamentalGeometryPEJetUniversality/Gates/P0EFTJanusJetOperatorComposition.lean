import Mathlib

namespace JanusFormal
namespace P0EFTJanusJetOperatorComposition

set_option autoImplicit false

universe u v w x y z t

/-- Abstract data needed to compose two finite-order differential operators at
the level of jet evaluators. The crucial datum is the holonomic prolongation from
a sufficiently high source jet into the jet of the lower-order source jet. -/
structure JetCompositionPresentation
    (SourceSections : Type u)
    (MiddleSections : Type v)
    (FirstJet : Type w)
    (MiddleJet : Type x)
    (CompositeJet : Type y)
    (ProlongedFirstJet : Type z)
    (Target : Type t) where
  firstJet : SourceSections → FirstJet
  middleJet : MiddleSections → MiddleJet
  compositeJet : SourceSections → CompositeJet
  holonomicProlongation : CompositeJet → ProlongedFirstJet
  prolongEvaluator :
    (FirstJet → MiddleSections) → ProlongedFirstJet → MiddleJet
  firstEvaluator : FirstJet → MiddleSections
  secondEvaluator : MiddleJet → Target
  firstOperator : SourceSections → MiddleSections
  secondOperator : MiddleSections → Target
  firstFactorization :
    ∀ source,
      firstOperator source = firstEvaluator (firstJet source)
  secondFactorization :
    ∀ middle,
      secondOperator middle = secondEvaluator (middleJet middle)
  prolongationCompatibility :
    ∀ source,
      prolongEvaluator firstEvaluator
          (holonomicProlongation (compositeJet source)) =
        middleJet (firstOperator source)

/-- Evaluator of the composite operator on the sufficiently high source jet. -/
def compositeEvaluator
    {SourceSections : Type u}
    {MiddleSections : Type v}
    {FirstJet : Type w}
    {MiddleJet : Type x}
    {CompositeJet : Type y}
    {ProlongedFirstJet : Type z}
    {Target : Type t}
    (presentation :
      JetCompositionPresentation
        SourceSections MiddleSections FirstJet MiddleJet
        CompositeJet ProlongedFirstJet Target) :
    CompositeJet → Target :=
  fun sourceJet =>
    presentation.secondEvaluator
      (presentation.prolongEvaluator presentation.firstEvaluator
        (presentation.holonomicProlongation sourceJet))

/-- Composition of finite-order operators factors through a higher source jet
by holonomic prolongation. Plain composition of maps between the unprolonged
standard fibers is therefore not the correct morphism law. -/
theorem composite_operator_factors_through_higher_jet
    {SourceSections : Type u}
    {MiddleSections : Type v}
    {FirstJet : Type w}
    {MiddleJet : Type x}
    {CompositeJet : Type y}
    {ProlongedFirstJet : Type z}
    {Target : Type t}
    (presentation :
      JetCompositionPresentation
        SourceSections MiddleSections FirstJet MiddleJet
        CompositeJet ProlongedFirstJet Target) :
    ∀ source,
      presentation.secondOperator
          (presentation.firstOperator source) =
        compositeEvaluator presentation
          (presentation.compositeJet source) := by
  intro source
  calc
    presentation.secondOperator
        (presentation.firstOperator source) =
      presentation.secondEvaluator
        (presentation.middleJet
          (presentation.firstOperator source)) :=
      presentation.secondFactorization _
    _ = presentation.secondEvaluator
        (presentation.prolongEvaluator presentation.firstEvaluator
          (presentation.holonomicProlongation
            (presentation.compositeJet source))) := by
      exact congrArg presentation.secondEvaluator
        (presentation.prolongationCompatibility source).symm
    _ = compositeEvaluator presentation
        (presentation.compositeJet source) := by
      rfl

/-- The categorical theorem requires more than objectwise representations: the
jet tower, holonomic composition, descent and the structured Janus groupoid must
all be supplied. -/
structure CategoricalJetEquivalenceStatus where
  regularLocalFiniteOrderCategoryDefined : Prop
  jetActionObjectsDefined : Prop
  holonomicJetCompositionDefined : Prop
  identityJetMorphismsDefined : Prop
  categoryLawsProved : Prop
  operatorToJetFunctorConstructed : Prop
  functorFaithful : Prop
  functorFull : Prop
  functorEssentiallySurjective : Prop
  structuredSpinCJetGroupoidConstructed : Prop
  globalTopologicalDataSeparated : Prop

/-- Closure of the classical/local categorical theorem together with the Janus
specialization data. -/
def categoricalJetEquivalenceClosed
    (s : CategoricalJetEquivalenceStatus) : Prop :=
  s.regularLocalFiniteOrderCategoryDefined /\
  s.jetActionObjectsDefined /\
  s.holonomicJetCompositionDefined /\
  s.identityJetMorphismsDefined /\
  s.categoryLawsProved /\
  s.operatorToJetFunctorConstructed /\
  s.functorFaithful /\
  s.functorFull /\
  s.functorEssentiallySurjective /\
  s.structuredSpinCJetGroupoidConstructed /\
  s.globalTopologicalDataSeparated

/-- A groupoid presentation of structured jets is an indispensable extra input
for the decorated SpinC-immersion specialization. -/
theorem missing_structured_jet_groupoid_blocks_categorical_specialization
    (s : CategoricalJetEquivalenceStatus)
    (hMissing : Not s.structuredSpinCJetGroupoidConstructed) :
    Not (categoricalJetEquivalenceClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end P0EFTJanusJetOperatorComposition
end JanusFormal

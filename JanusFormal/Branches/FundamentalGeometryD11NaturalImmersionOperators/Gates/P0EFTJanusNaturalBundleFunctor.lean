import Mathlib
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusSpinCImmersionCategory

namespace JanusFormal
namespace P0EFTJanusNaturalBundleFunctor

set_option autoImplicit false

open P0EFTJanusSpinCImmersionCategory

universe u v w x y

/-- Covariant fiber functor on admissible immersion morphisms. -/
structure NaturalBundleFunctor
    (immersionCategory : SpinCImmersionCategory) where
  Fiber : immersionCategory.category.Obj → Type w
  map :
    ∀ {source target},
      AdmissibleMorphism immersionCategory source target →
      Fiber source → Fiber target
  mapIdentity :
    ∀ object (value : Fiber object),
      map (admissibleIdentity immersionCategory object) value = value
  mapComposition :
    ∀ {first second third}
      (secondMorphism :
        AdmissibleMorphism immersionCategory second third)
      (firstMorphism :
        AdmissibleMorphism immersionCategory first second)
      (value : Fiber first),
      map (admissibleCompose immersionCategory
          secondMorphism firstMorphism) value =
        map secondMorphism (map firstMorphism value)

/-- Contravariant section functor, the correct variance for pullback. -/
structure NaturalSectionFunctor
    (immersionCategory : SpinCImmersionCategory) where
  Section : immersionCategory.category.Obj → Type x
  pullback :
    ∀ {source target},
      AdmissibleMorphism immersionCategory source target →
      Section target → Section source
  pullbackIdentity :
    ∀ object (sectionValue : Section object),
      pullback (admissibleIdentity immersionCategory object)
        sectionValue = sectionValue
  pullbackComposition :
    ∀ {first second third}
      (secondMorphism :
        AdmissibleMorphism immersionCategory second third)
      (firstMorphism :
        AdmissibleMorphism immersionCategory first second)
      (sectionValue : Section third),
      pullback (admissibleCompose immersionCategory
          secondMorphism firstMorphism) sectionValue =
        pullback firstMorphism
          (pullback secondMorphism sectionValue)

/-- Natural differential operator before order/locality data are attached. -/
structure NaturalOperator
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor : NaturalSectionFunctor immersionCategory)
    (targetFunctor : NaturalSectionFunctor immersionCategory) where
  apply :
    ∀ object,
      sourceFunctor.Section object →
      targetFunctor.Section object
  naturality :
    ∀ {source target}
      (morphism :
        AdmissibleMorphism immersionCategory source target)
      (sectionValue : sourceFunctor.Section target),
      targetFunctor.pullback morphism
          (apply target sectionValue) =
        apply source
          (sourceFunctor.pullback morphism sectionValue)

/-- Identity natural operator. -/
def identityNaturalOperator
    (immersionCategory : SpinCImmersionCategory)
    (sectionFunctor : NaturalSectionFunctor immersionCategory) :
    NaturalOperator immersionCategory sectionFunctor sectionFunctor where
  apply := fun _ sectionValue => sectionValue
  naturality := by
    intro source target morphism sectionValue
    rfl

/-- Composition of natural operators. -/
def composeNaturalOperators
    (immersionCategory : SpinCImmersionCategory)
    (firstFunctor secondFunctor thirdFunctor :
      NaturalSectionFunctor immersionCategory)
    (secondOperator :
      NaturalOperator immersionCategory secondFunctor thirdFunctor)
    (firstOperator :
      NaturalOperator immersionCategory firstFunctor secondFunctor) :
    NaturalOperator immersionCategory firstFunctor thirdFunctor where
  apply := fun object sectionValue =>
    secondOperator.apply object
      (firstOperator.apply object sectionValue)
  naturality := by
    intro source target morphism sectionValue
    rw [secondOperator.naturality]
    rw [firstOperator.naturality]

/-- Pointwise product of two section functors. -/
def productSectionFunctor
    (immersionCategory : SpinCImmersionCategory)
    (firstFunctor : NaturalSectionFunctor immersionCategory)
    (secondFunctor : NaturalSectionFunctor immersionCategory) :
    NaturalSectionFunctor immersionCategory where
  Section := fun object =>
    firstFunctor.Section object × secondFunctor.Section object
  pullback := fun morphism sectionValue =>
    (firstFunctor.pullback morphism sectionValue.1,
      secondFunctor.pullback morphism sectionValue.2)
  pullbackIdentity := by
    intro object sectionValue
    apply Prod.ext
    · exact firstFunctor.pullbackIdentity object sectionValue.1
    · exact secondFunctor.pullbackIdentity object sectionValue.2
  pullbackComposition := by
    intro first second third secondMorphism firstMorphism sectionValue
    apply Prod.ext
    · exact firstFunctor.pullbackComposition
        secondMorphism firstMorphism sectionValue.1
    · exact secondFunctor.pullbackComposition
        secondMorphism firstMorphism sectionValue.2

/-- Product of two natural operators with a common source. -/
def pairNaturalOperators
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor firstTarget secondTarget :
      NaturalSectionFunctor immersionCategory)
    (firstOperator :
      NaturalOperator immersionCategory sourceFunctor firstTarget)
    (secondOperator :
      NaturalOperator immersionCategory sourceFunctor secondTarget) :
    NaturalOperator immersionCategory sourceFunctor
      (productSectionFunctor immersionCategory firstTarget secondTarget) where
  apply := fun object sectionValue =>
    (firstOperator.apply object sectionValue,
      secondOperator.apply object sectionValue)
  naturality := by
    intro source target morphism sectionValue
    apply Prod.ext
    · exact firstOperator.naturality morphism sectionValue
    · exact secondOperator.naturality morphism sectionValue

/-- First projection is natural. -/
def firstProjectionNaturalOperator
    (immersionCategory : SpinCImmersionCategory)
    (firstFunctor secondFunctor :
      NaturalSectionFunctor immersionCategory) :
    NaturalOperator immersionCategory
      (productSectionFunctor immersionCategory firstFunctor secondFunctor)
      firstFunctor where
  apply := fun _ sectionValue => sectionValue.1
  naturality := by
    intro source target morphism sectionValue
    rfl

/-- Second projection is natural. -/
def secondProjectionNaturalOperator
    (immersionCategory : SpinCImmersionCategory)
    (firstFunctor secondFunctor :
      NaturalSectionFunctor immersionCategory) :
    NaturalOperator immersionCategory
      (productSectionFunctor immersionCategory firstFunctor secondFunctor)
      secondFunctor where
  apply := fun _ sectionValue => sectionValue.2
  naturality := by
    intro source target morphism sectionValue
    rfl

/-- Pairing followed by projection recovers the first operator. -/
theorem first_projection_pair
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor firstTarget secondTarget :
      NaturalSectionFunctor immersionCategory)
    (firstOperator :
      NaturalOperator immersionCategory sourceFunctor firstTarget)
    (secondOperator :
      NaturalOperator immersionCategory sourceFunctor secondTarget)
    (object : immersionCategory.category.Obj)
    (sectionValue : sourceFunctor.Section object) :
    (composeNaturalOperators immersionCategory
      (productSectionFunctor immersionCategory firstTarget secondTarget)
      firstTarget firstTarget
      (identityNaturalOperator immersionCategory firstTarget)
      (firstProjectionNaturalOperator immersionCategory
        firstTarget secondTarget)).apply object
      ((pairNaturalOperators immersionCategory sourceFunctor
        firstTarget secondTarget firstOperator secondOperator).apply
        object sectionValue) =
      firstOperator.apply object sectionValue := by
  rfl

/--
The categorical theory fixes functoriality and covariance.  It does not yet say
that an operator is differential or finite-order; those are additional locality
and jet-factorization theorems handled separately.
-/
structure NaturalBundleFunctorPhysicalStatus where
  tangentBundleFunctorConstructed : Prop
  normalBundleFunctorConstructed : Prop
  tensorBundleFunctorsConstructed : Prop
  spinorFunctorConstructed : Prop
  monopoleTwistFunctorConstructed : Prop
  normalRootTwistFunctorConstructed : Prop
  gaugeAndGhostFunctorsConstructed : Prop
  sectionPullbacksConstructed : Prop
  functorLawsProved : Prop


def naturalBundleFunctorPhysicalClosure
    (s : NaturalBundleFunctorPhysicalStatus) : Prop :=
  s.tangentBundleFunctorConstructed /\
  s.normalBundleFunctorConstructed /\
  s.tensorBundleFunctorsConstructed /\
  s.spinorFunctorConstructed /\
  s.monopoleTwistFunctorConstructed /\
  s.normalRootTwistFunctorConstructed /\
  s.gaugeAndGhostFunctorsConstructed /\
  s.sectionPullbacksConstructed /\
  s.functorLawsProved

end P0EFTJanusNaturalBundleFunctor
end JanusFormal

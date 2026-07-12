import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpinCImmersionCategory

set_option autoImplicit false

universe u v

/-- Minimal category interface used by Program D11. -/
structure SmallCategoryData where
  Obj : Type u
  Hom : Obj → Obj → Type v
  identity : ∀ object, Hom object object
  compose :
    ∀ {first second third},
      Hom second third → Hom first second → Hom first third
  identity_compose :
    ∀ {first second} (morphism : Hom first second),
      compose (identity second) morphism = morphism
  compose_identity :
    ∀ {first second} (morphism : Hom first second),
      compose morphism (identity first) = morphism
  compose_assoc :
    ∀ {first second third fourth}
      (thirdMorphism : Hom third fourth)
      (secondMorphism : Hom second third)
      (firstMorphism : Hom first second),
      compose (compose thirdMorphism secondMorphism) firstMorphism =
        compose thirdMorphism (compose secondMorphism firstMorphism)

/-- Geometric data carried by one object of the immersion category. -/
structure SpinCImmersionGeometry where
  throatDimension : ℕ
  ambientDimension : ℕ
  codimensionOne : ambientDimension = throatDimension + 1
  compactWithoutBoundary : Prop
  immersionConstructed : Prop
  inducedRiemannianMetricConstructed : Prop
  tangentNormalExactSequenceConstructed : Prop
  spinStructureConstructed : Prop
  primitiveTwistingLineConstructed : Prop
  normalLineConstructed : Prop
  normalLineNontrivial : Prop
  normalRootFlatLineConstructed : Prop
  gaugeConnectionConstructed : Prop

/-- Category of decorated SpinC immersions and admissible structure-preserving morphisms. -/
structure SpinCImmersionCategory where
  category : SmallCategoryData
  geometry : category.Obj → SpinCImmersionGeometry
  admissible :
    ∀ {source target},
      category.Hom source target → Prop
  identityAdmissible :
    ∀ object,
      admissible (category.identity object)
  compositionAdmissible :
    ∀ {first second third}
      (secondMorphism : category.Hom second third)
      (firstMorphism : category.Hom first second),
      admissible secondMorphism →
      admissible firstMorphism →
      admissible
        (category.compose secondMorphism firstMorphism)

/-- Admissible morphism with its preservation certificate. -/
structure AdmissibleMorphism
    (immersionCategory : SpinCImmersionCategory)
    (source target : immersionCategory.category.Obj) where
  morphism : immersionCategory.category.Hom source target
  preservation : immersionCategory.admissible morphism

/-- Identity admissible morphism. -/
def admissibleIdentity
    (immersionCategory : SpinCImmersionCategory)
    (object : immersionCategory.category.Obj) :
    AdmissibleMorphism immersionCategory object object :=
  { morphism := immersionCategory.category.identity object
    preservation := immersionCategory.identityAdmissible object }

/-- Composition of admissible morphisms. -/
def admissibleCompose
    (immersionCategory : SpinCImmersionCategory)
    {first second third : immersionCategory.category.Obj}
    (secondMorphism :
      AdmissibleMorphism immersionCategory second third)
    (firstMorphism :
      AdmissibleMorphism immersionCategory first second) :
    AdmissibleMorphism immersionCategory first third :=
  { morphism := immersionCategory.category.compose
      secondMorphism.morphism firstMorphism.morphism
    preservation := immersionCategory.compositionAdmissible
      secondMorphism.morphism firstMorphism.morphism
      secondMorphism.preservation firstMorphism.preservation }

/-- Underlying morphism of left identity composition. -/
theorem admissible_identity_compose
    (immersionCategory : SpinCImmersionCategory)
    {source target : immersionCategory.category.Obj}
    (morphism : AdmissibleMorphism immersionCategory source target) :
    (admissibleCompose immersionCategory
      (admissibleIdentity immersionCategory target)
      morphism).morphism = morphism.morphism := by
  exact immersionCategory.category.identity_compose morphism.morphism

/-- Underlying morphism of right identity composition. -/
theorem admissible_compose_identity
    (immersionCategory : SpinCImmersionCategory)
    {source target : immersionCategory.category.Obj}
    (morphism : AdmissibleMorphism immersionCategory source target) :
    (admissibleCompose immersionCategory
      morphism
      (admissibleIdentity immersionCategory source)).morphism =
        morphism.morphism := by
  exact immersionCategory.category.compose_identity morphism.morphism

/-- Associativity of admissible composition at the underlying morphism level. -/
theorem admissible_compose_assoc
    (immersionCategory : SpinCImmersionCategory)
    {first second third fourth : immersionCategory.category.Obj}
    (thirdMorphism :
      AdmissibleMorphism immersionCategory third fourth)
    (secondMorphism :
      AdmissibleMorphism immersionCategory second third)
    (firstMorphism :
      AdmissibleMorphism immersionCategory first second) :
    (admissibleCompose immersionCategory
      (admissibleCompose immersionCategory
        thirdMorphism secondMorphism)
      firstMorphism).morphism =
    (admissibleCompose immersionCategory
      thirdMorphism
      (admissibleCompose immersionCategory
        secondMorphism firstMorphism)).morphism := by
  exact immersionCategory.category.compose_assoc
    thirdMorphism.morphism secondMorphism.morphism firstMorphism.morphism

/-- One-object category, useful as the categorical shell of a fixed Janus background. -/
def oneObjectCategory : SmallCategoryData where
  Obj := Unit
  Hom := fun _ _ => Unit
  identity := fun _ => ()
  compose := fun _ _ => ()
  identity_compose := by
    intro first second morphism
    cases morphism
    rfl
  compose_identity := by
    intro first second morphism
    cases morphism
    rfl
  compose_assoc := by
    intro first second third fourth thirdMorphism secondMorphism firstMorphism
    cases thirdMorphism
    cases secondMorphism
    cases firstMorphism
    rfl

/-- Every geometric package defines at least a one-object decorated category. -/
def fixedGeometryCategory
    (geometry : SpinCImmersionGeometry) : SpinCImmersionCategory where
  category := oneObjectCategory
  geometry := fun _ => geometry
  admissible := fun _ => True
  identityAdmissible := by
    intro object
    trivial
  compositionAdmissible := by
    intro first second third secondMorphism firstMorphism
      hSecond hFirst
    trivial

/-- The categorical shell exists once one decorated immersion object exists. -/
theorem fixed_geometry_category_exists
    (geometry : SpinCImmersionGeometry) :
    ∃ immersionCategory : SpinCImmersionCategory,
      immersionCategory.geometry () = geometry := by
  exact ⟨fixedGeometryCategory geometry, rfl⟩

/--
The one-object construction proves existence of a categorical shell, not of the
full moduli category.  A genuine D11 globalization must construct all nearby
immersions and their structure-preserving morphisms, together with a topology
or smooth/derived structure on the object space.
-/
structure SpinCImmersionModuliCategoryStatus where
  objectClassDefined : Prop
  admissibleMorphismsDefined : Prop
  identitiesAndCompositionConstructed : Prop
  categoryLawsProved : Prop
  diffeomorphismActionIncluded : Prop
  gaugeActionIncluded : Prop
  familiesAndBaseChangeDefined : Prop
  smoothOrDerivedStackConstructed : Prop


def spinCImmersionModuliCategoryClosed
    (s : SpinCImmersionModuliCategoryStatus) : Prop :=
  s.objectClassDefined /\
  s.admissibleMorphismsDefined /\
  s.identitiesAndCompositionConstructed /\
  s.categoryLawsProved /\
  s.diffeomorphismActionIncluded /\
  s.gaugeActionIncluded /\
  s.familiesAndBaseChangeDefined /\
  s.smoothOrDerivedStackConstructed

end P0EFTJanusSpinCImmersionCategory
end JanusFormal

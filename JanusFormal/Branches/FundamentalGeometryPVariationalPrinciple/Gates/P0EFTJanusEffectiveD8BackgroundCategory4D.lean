import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedD8DiffeomorphismCategory4D

/-!
# Category of effective D8 backgrounds

The period is promoted from a fixed parameter to object data.  Morphisms are
genuine smooth diffeomorphisms between the corresponding effective quotients,
and smooth coefficient fields form the expected contravariant functor.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8BackgroundCategory4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusFixedD8DiffeomorphismCategory4D

/-- Object data for the effective D8 family. -/
structure EffectiveD8Background where
  period : Real
  period_ne_zero : period ≠ 0

private abbrev EffectiveQuotient (background : EffectiveD8Background) :=
  MappingTorus
    (reflectedSphereData background.period background.period_ne_zero)

local instance effectiveQuotientChartedSpace
    (background : EffectiveD8Background) :
    ChartedSpace CoverModel (EffectiveQuotient background) :=
  reflectedSphereQuotientChartedSpace
    background.period background.period_ne_zero

local instance effectiveQuotientIsManifold
    (background : EffectiveD8Background) :
    IsManifold coverModelWithCorners ω (EffectiveQuotient background) :=
  reflectedSphereQuotient_isManifold
    background.period background.period_ne_zero

/-- Genuine smooth morphisms between two effective backgrounds. -/
abbrev EffectiveD8BackgroundDiffeomorphism
    (source target : EffectiveD8Background) :=
  EffectiveQuotient source ≃ₘ^ω⟮coverModelWithCorners,
    coverModelWithCorners⟯ EffectiveQuotient target

/-- Category containing the whole nonzero-period D8 family as objects. -/
def effectiveD8BackgroundCategoryData : SmallCategoryData where
  Obj := EffectiveD8Background
  Hom := EffectiveD8BackgroundDiffeomorphism
  identity := fun background =>
    Diffeomorph.refl coverModelWithCorners (EffectiveQuotient background) ω
  compose := fun secondMorphism firstMorphism =>
    firstMorphism.trans secondMorphism
  identity_compose := by
    intro first second morphism
    ext point
    rfl
  compose_identity := by
    intro first second morphism
    ext point
    rfl
  compose_assoc := by
    intro first second third fourth thirdMorphism secondMorphism firstMorphism
    ext point
    rfl

/-- The effective geometry status is uniform over every object. -/
def effectiveD8BackgroundCategory : SpinCImmersionCategory where
  category := effectiveD8BackgroundCategoryData
  geometry := fun _ => fixedD8ImmersionGeometry
  admissible := fun _ => True
  identityAdmissible := by
    intro
    trivial
  compositionAdmissible := by
    intro first second third secondMorphism firstMorphism hSecond hFirst
    trivial

universe u

/-- Pullback of a smooth field along a morphism between possibly different
effective D8 backgrounds. -/
def pullbackEffectiveD8SmoothField
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : SmoothQuotientField target.period target.period_ne_zero Fiber) :
    SmoothQuotientField source.period source.period_ne_zero Fiber where
  toFun := field.toFun ∘ morphism
  contMDiff_toFun := field.contMDiff_toFun.comp
    (morphism.contMDiff.of_le (by simp))

@[simp] theorem pullbackEffectiveD8SmoothField_apply
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : SmoothQuotientField target.period target.period_ne_zero Fiber)
    (point : EffectiveQuotient source) :
    pullbackEffectiveD8SmoothField Fiber morphism field point =
      field (morphism point) :=
  rfl

/-- Pullback along the categorical identity is literally the original field. -/
theorem pullbackEffectiveD8SmoothField_refl
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (background : EffectiveD8Background)
    (field : SmoothQuotientField background.period
      background.period_ne_zero Fiber) :
    pullbackEffectiveD8SmoothField Fiber
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) field = field := by
  apply SmoothQuotientField.ext
  intro point
  rfl

/-- Pullback is contravariantly compatible with composition between three
possibly different effective backgrounds. -/
theorem pullbackEffectiveD8SmoothField_trans
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (field : SmoothQuotientField target.period target.period_ne_zero Fiber) :
    pullbackEffectiveD8SmoothField Fiber first
        (pullbackEffectiveD8SmoothField Fiber second field) =
      pullbackEffectiveD8SmoothField Fiber (first.trans second) field := by
  apply SmoothQuotientField.ext
  intro point
  rfl

/-- Smooth fields are a contravariant natural section functor on the whole
effective-background category. -/
def effectiveD8SmoothFieldSectionFunctor
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :
    NaturalSectionFunctor effectiveD8BackgroundCategory where
  Section := fun background =>
    SmoothQuotientField background.period background.period_ne_zero Fiber
  pullback := fun morphism field =>
    pullbackEffectiveD8SmoothField Fiber morphism.morphism field
  pullbackIdentity := by
    intro background field
    exact pullbackEffectiveD8SmoothField_refl Fiber background field
  pullbackComposition := by
    intro first second third secondMorphism firstMorphism field
    exact (pullbackEffectiveD8SmoothField_trans Fiber
      firstMorphism.morphism secondMorphism.morphism field).symm

/-- Scalar fields are the real-coefficient specialization. -/
def effectiveD8SmoothScalarSectionFunctor :
    NaturalSectionFunctor effectiveD8BackgroundCategory :=
  effectiveD8SmoothFieldSectionFunctor Real

/-- The identity scalar operator is natural across the full background
category. -/
def effectiveD8SmoothScalarIdentityNaturalOperator :
    NaturalOperator effectiveD8BackgroundCategory
      effectiveD8SmoothScalarSectionFunctor
      effectiveD8SmoothScalarSectionFunctor :=
  identityNaturalOperator effectiveD8BackgroundCategory
    effectiveD8SmoothScalarSectionFunctor

end

end P0EFTJanusEffectiveD8BackgroundCategory4D
end JanusFormal

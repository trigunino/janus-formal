import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalBundleFunctor
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

/-!
# Fixed-background D8 diffeomorphism category

The single effective D8 spacetime is made into a genuine one-object category
whose morphisms are all smooth self-diffeomorphisms, not a trivial one-arrow
shell.  Smooth coefficient fields form a contravariant section functor via
pullback, with identity and composition laws inherited from the actual D8
pullback operation.

This is the symmetry category of one fixed background.  It is not the moduli
category of all Janus geometries or a smooth/derived stack.
-/

namespace JanusFormal
namespace P0EFTJanusFixedD8DiffeomorphismCategory4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One-object category with the full smooth D8 self-diffeomorphism group as
its morphisms.  Categorical composition is ordinary map composition. -/
def fixedD8DiffeomorphismCategoryData : SmallCategoryData where
  Obj := Unit
  Hom := fun _ _ => SpacetimeDiffeomorphism period hPeriod
  identity := fun _ =>
    Diffeomorph.refl coverModelWithCorners (EffectiveQuotient period hPeriod) ω
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

/-- Honest geometric status of the fixed D8 object.  Fields not yet globally
constructed are recorded as propositions, not asserted as theorems. -/
def fixedD8ImmersionGeometry : SpinCImmersionGeometry where
  throatDimension := 3
  ambientDimension := 4
  codimensionOne := rfl
  compactWithoutBoundary := True
  immersionConstructed := True
  inducedRiemannianMetricConstructed := True
  tangentNormalExactSequenceConstructed := True
  spinStructureConstructed := False
  primitiveTwistingLineConstructed := False
  normalLineConstructed := True
  normalLineNontrivial := True
  normalRootFlatLineConstructed := True
  gaugeConnectionConstructed := True

/-- The fixed-background Janus symmetry category. -/
def fixedD8DiffeomorphismCategory : SpinCImmersionCategory where
  category := fixedD8DiffeomorphismCategoryData period hPeriod
  geometry := fun _ => fixedD8ImmersionGeometry
  admissible := fun _ => True
  identityAdmissible := by
    intro object
    trivial
  compositionAdmissible := by
    intro first second third secondMorphism firstMorphism hSecond hFirst
    trivial

universe u

/-- Smooth fields with any normed real coefficient fiber form a genuine
contravariant functor on the fixed D8 diffeomorphism category. -/
def fixedD8SmoothFieldSectionFunctor
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :
    NaturalSectionFunctor (fixedD8DiffeomorphismCategory period hPeriod) where
  Section := fun _ => SmoothQuotientField period hPeriod Fiber
  pullback := fun morphism field =>
    pullbackSmoothField period hPeriod Fiber morphism.morphism field
  pullbackIdentity := by
    intro object field
    exact pullbackSmoothField_refl period hPeriod Fiber field
  pullbackComposition := by
    intro first second third secondMorphism firstMorphism field
    exact (pullbackSmoothField_trans period hPeriod Fiber
      firstMorphism.morphism secondMorphism.morphism field).symm

/-- Scalar coefficient fields are the real-fiber specialization. -/
def fixedD8SmoothScalarSectionFunctor :
    NaturalSectionFunctor (fixedD8DiffeomorphismCategory period hPeriod) :=
  fixedD8SmoothFieldSectionFunctor period hPeriod Real

/-- The identity scalar operator is natural for every actual smooth D8
self-diffeomorphism. -/
def fixedD8SmoothScalarIdentityNaturalOperator :
    NaturalOperator (fixedD8DiffeomorphismCategory period hPeriod)
      (fixedD8SmoothScalarSectionFunctor period hPeriod)
      (fixedD8SmoothScalarSectionFunctor period hPeriod) :=
  identityNaturalOperator (fixedD8DiffeomorphismCategory period hPeriod)
    (fixedD8SmoothScalarSectionFunctor period hPeriod)

end

end P0EFTJanusFixedD8DiffeomorphismCategory4D
end JanusFormal

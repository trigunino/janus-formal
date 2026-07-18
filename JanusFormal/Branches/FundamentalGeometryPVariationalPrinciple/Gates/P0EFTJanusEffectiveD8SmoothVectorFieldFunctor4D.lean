import Mathlib.Geometry.Manifold.VectorField.Pullback
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8BackgroundCategory4D

/-!
# Smooth tangent-vector fields on the global effective D8 category

Every effective background carries its genuine tangent bundle.  A smooth
background diffeomorphism acts contravariantly on smooth vector fields through
Mathlib's intrinsic manifold pullback.  The construction is smooth, local and
satisfies exact identity and composition laws between arbitrary nonzero
periods.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusEffectiveD8BackgroundCategory4D

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

/-- Genuine smooth sections of the tangent bundle of an effective D8
background. -/
abbrev EffectiveD8SmoothVectorField (background : EffectiveD8Background) :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (fun point : EffectiveQuotient background =>
      TangentSpace coverModelWithCorners point)

/-- Intrinsic contravariant pullback of a smooth tangent-vector field. -/
def effectiveD8SmoothVectorFieldPullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothVectorField target) :
    EffectiveD8SmoothVectorField source where
  toFun := VectorField.mpullback coverModelWithCorners coverModelWithCorners
    morphism field
  contMDiff_toFun := by
    apply field.contMDiff.mpullback_vectorField morphism.contMDiff
    · intro point
      rw [← morphism.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact ContinuousLinearMap.isInvertible_equiv
    · simp

@[simp] theorem effectiveD8SmoothVectorFieldPullback_apply
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : EffectiveD8SmoothVectorField target)
    (point : EffectiveQuotient source) :
    effectiveD8SmoothVectorFieldPullback morphism field point =
      VectorField.mpullback coverModelWithCorners coverModelWithCorners
        morphism field point :=
  rfl

/-- Pullback by the identity background diffeomorphism is exact. -/
theorem effectiveD8SmoothVectorFieldPullback_refl
    (background : EffectiveD8Background)
    (field : EffectiveD8SmoothVectorField background) :
    effectiveD8SmoothVectorFieldPullback
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient background) ω) field = field := by
  apply ContMDiffSection.ext
  intro point
  simpa [effectiveD8SmoothVectorFieldPullback] using
    congrFun (VectorField.mpullback_id
      (I := coverModelWithCorners) (V := fun x => field x)) point

/-- Smooth vector-field pullback is contravariantly functorial across three
arbitrary effective D8 backgrounds. -/
theorem effectiveD8SmoothVectorFieldPullback_trans
    {source middle target : EffectiveD8Background}
    (first : EffectiveD8BackgroundDiffeomorphism source middle)
    (second : EffectiveD8BackgroundDiffeomorphism middle target)
    (field : EffectiveD8SmoothVectorField target) :
    effectiveD8SmoothVectorFieldPullback first
        (effectiveD8SmoothVectorFieldPullback second field) =
      effectiveD8SmoothVectorFieldPullback (first.trans second) field := by
  apply ContMDiffSection.ext
  intro point
  have hFirst : MDifferentiableWithinAt coverModelWithCorners
      coverModelWithCorners first Set.univ point :=
    first.contMDiff.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
  have hSecondInvertible :
      (mfderivWithin coverModelWithCorners coverModelWithCorners
        second Set.univ (first point)).IsInvertible := by
    rw [mfderivWithin_univ,
      ← second.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact ContinuousLinearMap.isInvertible_equiv
  have hComposition := VectorField.mpullbackWithin_comp_of_left
    (I := coverModelWithCorners) (I' := coverModelWithCorners)
    (I'' := coverModelWithCorners) (f := first) (g := second)
    (V := fun x => field x) (s := Set.univ) (t := Set.univ)
    (x₀ := point) hFirst (Set.mapsTo_univ first Set.univ)
    (uniqueMDiffWithinAt_univ coverModelWithCorners)
    hSecondInvertible
  simpa [effectiveD8SmoothVectorFieldPullback, Function.comp_def] using
    hComposition.symm

/-- Pointwise locality: pullback at a point depends only on the target vector
field at the image point. -/
theorem effectiveD8SmoothVectorFieldPullback_congr_at
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (first second : EffectiveD8SmoothVectorField target)
    (point : EffectiveQuotient source)
    (hField : first (morphism point) = second (morphism point)) :
    effectiveD8SmoothVectorFieldPullback morphism first point =
      effectiveD8SmoothVectorFieldPullback morphism second point := by
  simp only [effectiveD8SmoothVectorFieldPullback_apply,
    VectorField.mpullback_apply]
  rw [hField]

/-- Sheaf locality on inverse images. -/
theorem effectiveD8SmoothVectorFieldPullback_congr_on_preimage
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (first second : EffectiveD8SmoothVectorField target)
    (region : Set (EffectiveQuotient target))
    (hField : ∀ point ∈ region, first point = second point)
    (point : EffectiveQuotient source)
    (hPoint : morphism point ∈ region) :
    effectiveD8SmoothVectorFieldPullback morphism first point =
      effectiveD8SmoothVectorFieldPullback morphism second point :=
  effectiveD8SmoothVectorFieldPullback_congr_at morphism first second point
    (hField (morphism point) hPoint)

/-- Smooth tangent-vector fields form a contravariant natural section functor
on the full effective-background category. -/
def effectiveD8SmoothVectorFieldSectionFunctor :
    NaturalSectionFunctor effectiveD8BackgroundCategory where
  Section := EffectiveD8SmoothVectorField
  pullback := fun morphism field =>
    effectiveD8SmoothVectorFieldPullback morphism.morphism field
  pullbackIdentity := by
    intro background field
    exact effectiveD8SmoothVectorFieldPullback_refl background field
  pullbackComposition := by
    intro source middle target secondMorphism firstMorphism field
    exact (effectiveD8SmoothVectorFieldPullback_trans
      firstMorphism.morphism secondMorphism.morphism field).symm

end

end P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
end JanusFormal

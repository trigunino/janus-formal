import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

/-!
# Natural holonomic scalar differential on the effective D8 family

The manifold differential of a smooth scalar is promoted to a genuine smooth
one-form section.  This construction commutes exactly with pullback between
arbitrary nonzero-period effective backgrounds.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

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

/-- The differential of a smooth scalar as a genuine smooth global one-form. -/
def effectiveD8SmoothScalarDifferential
    (background : EffectiveD8Background)
    (field : SmoothQuotientField background.period
      background.period_ne_zero Real) :
    EffectiveD8SmoothCovectorField background where
  toFun := fun point =>
    mfderiv coverModelWithCorners 𝓘(Real, Real) field point
  contMDiff_toFun := by
    intro point
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hD := field.contMDiff_toFun.contMDiffAt.mfderiv_const
      (x₀ := point) (m := ∞) (by simp)
    apply hD.congr_of_eventuallyEq
    filter_upwards [] with current
    change ContinuousLinearMap.inCoordinates CoverCoordinates
        (TangentSpace coverModelWithCorners)
        Real (fun _ : EffectiveQuotient background => Real)
        point current point current
          (mfderiv coverModelWithCorners 𝓘(Real, Real) field current) = _
    apply ContinuousLinearMap.ext
    intro vector
    simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rw [ContinuousLinearMap.one_def]
    rfl

@[simp] theorem effectiveD8SmoothScalarDifferential_apply
    (background : EffectiveD8Background)
    (field : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background) :
    effectiveD8SmoothScalarDifferential background field point =
      mfderiv coverModelWithCorners 𝓘(Real, Real) field point :=
  rfl

/-- The global scalar differential commutes exactly with effective D8
pullback. -/
theorem effectiveD8SmoothScalarDifferential_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (field : SmoothQuotientField target.period target.period_ne_zero Real) :
    effectiveD8SmoothScalarDifferential source
        (pullbackEffectiveD8SmoothField Real morphism field) =
      effectiveD8SmoothCovectorFieldPullback morphism
        (effectiveD8SmoothScalarDifferential target field) := by
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro tangent
  have hOuter := field.contMDiff_toFun.mdifferentiableAt
    (x := morphism point) (by simp)
  have hInner := morphism.contMDiff.mdifferentiableAt
    (x := point) (by simp)
  change mfderiv coverModelWithCorners 𝓘(Real, Real)
      (field.toFun ∘ morphism) point tangent =
    mfderiv coverModelWithCorners 𝓘(Real, Real) field
      (morphism point)
      (mfderiv coverModelWithCorners coverModelWithCorners morphism point
        tangent)
  rw [mfderiv_comp point hOuter hInner]
  rfl

end

end P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
end JanusFormal

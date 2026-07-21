import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D

/-!
# Smooth scalar differentials and gradients on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothScalarGradient4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
open P0EFTJanusMappingTorusCutBulkSmoothInverseMusical4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

/-- Genuine smooth scalar fields on the cut bulk. -/
structure CutBulkSmoothScalarField where
  toFun : PositiveHemisphereCutBulk period hPeriod → Real
  contMDiff_toFun :
    ContMDiff cutCollarModelWithCorners 𝓘(Real, Real) ∞ toFun

instance : CoeFun (CutBulkSmoothScalarField period hPeriod)
    (fun _ => PositiveHemisphereCutBulk period hPeriod → Real) :=
  ⟨CutBulkSmoothScalarField.toFun⟩

/-- Pullback of an ambient quotient scalar to the cut bulk. -/
def cutBulkSmoothScalarPullback
    (field : SmoothQuotientField period hPeriod Real) :
    CutBulkSmoothScalarField period hPeriod where
  toFun := field ∘ cutBulkToAmbient period hPeriod
  contMDiff_toFun := field.contMDiff_toFun.comp
    (cutBulkToAmbient_contMDiff period hPeriod)

@[simp]
theorem cutBulkSmoothScalarPullback_apply
    (field : SmoothQuotientField period hPeriod Real)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    cutBulkSmoothScalarPullback period hPeriod field point =
      field (cutBulkToAmbient period hPeriod point) :=
  rfl

/-- Differential of a smooth cut-bulk scalar as a smooth one-form. -/
def cutBulkSmoothScalarDifferential
    (field : CutBulkSmoothScalarField period hPeriod) :
    CutBulkSmoothCovectorField period hPeriod where
  toFun := fun point =>
    mfderiv cutCollarModelWithCorners 𝓘(Real, Real) field point
  contMDiff_toFun := by
    intro point
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hD := field.contMDiff_toFun.contMDiffAt.mfderiv_const
      (x₀ := point) (m := ∞) (by simp)
    apply hD.congr_of_eventuallyEq
    filter_upwards [] with current
    change ContinuousLinearMap.inCoordinates CutCollarCoordinates
        (TangentSpace cutCollarModelWithCorners)
        Real (fun _ : PositiveHemisphereCutBulk period hPeriod => Real)
        point current point current
          (mfderiv cutCollarModelWithCorners 𝓘(Real, Real) field current) = _
    apply ContinuousLinearMap.ext
    intro vector
    simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rw [ContinuousLinearMap.one_def]
    rfl

@[simp]
theorem cutBulkSmoothScalarDifferential_apply
    (field : CutBulkSmoothScalarField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    cutBulkSmoothScalarDifferential period hPeriod field point =
      mfderiv cutCollarModelWithCorners 𝓘(Real, Real) field point :=
  rfl

/-- Chain rule for the ambient scalar pullback. -/
theorem cutBulkSmoothScalarDifferential_pullback
    (field : SmoothQuotientField period hPeriod Real)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    cutBulkSmoothScalarDifferential period hPeriod
        (cutBulkSmoothScalarPullback period hPeriod field) point =
      (mfderiv coverModelWithCorners 𝓘(Real, Real) field
        (cutBulkToAmbient period hPeriod point)).comp
        (mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkToAmbient period hPeriod) point) := by
  have hOuter := field.contMDiff_toFun.mdifferentiableAt
    (x := cutBulkToAmbient period hPeriod point) (by simp)
  have hInner := (cutBulkToAmbient_contMDiff period hPeriod).mdifferentiableAt
    (x := point) (by simp)
  change mfderiv cutCollarModelWithCorners 𝓘(Real, Real)
      (field.toFun ∘ cutBulkToAmbient period hPeriod) point = _
  exact mfderiv_comp point hOuter hInner

/-- Smooth metric gradient of a smooth cut-bulk scalar. -/
def cutBulkSmoothScalarGradient
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (field : CutBulkSmoothScalarField period hPeriod) :
    CutBulkSmoothVectorField period hPeriod :=
  cutBulkSmoothInverseMusical period hPeriod metric
    (cutBulkSmoothScalarDifferential period hPeriod field)

theorem cutBulkSmoothScalarGradient_flat
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (field : CutBulkSmoothScalarField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    metric.musical point
        (cutBulkSmoothScalarGradient period hPeriod metric field point) =
      cutBulkSmoothScalarDifferential period hPeriod field point :=
  cutBulkSmoothInverseMusical_flat period hPeriod metric
    (cutBulkSmoothScalarDifferential period hPeriod field) point

end
end P0EFTJanusMappingTorusCutBulkSmoothScalarGradient4D
end JanusFormal

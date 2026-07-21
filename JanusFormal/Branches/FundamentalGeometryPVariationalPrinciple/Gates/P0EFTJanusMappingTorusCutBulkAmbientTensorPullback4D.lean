import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D

/-!
# Pointwise ambient tensor pullback to the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance quotientIsManifold :
    IsManifold coverModelWithCorners ∞ (EffectiveQuotient period hPeriod) :=
  (reflectedSphereQuotient_isManifold period hPeriod).of_le le_top

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

abbrev CutBulkTangentFiber
    (point : PositiveHemisphereCutBulk period hPeriod) :=
  TangentSpace cutCollarModelWithCorners point

abbrev CutBulkCovariantTwoTensorFiber
    (point : PositiveHemisphereCutBulk period hPeriod) :=
  CutBulkTangentFiber period hPeriod point →L[Real]
    CutBulkTangentFiber period hPeriod point →L[Real] Real

abbrev CutBulkCovariantTwoTensorField :=
  ∀ point, CutBulkCovariantTwoTensorFiber period hPeriod point

theorem cutBulkToAmbient_mdifferentiable :
    MDifferentiable cutCollarModelWithCorners coverModelWithCorners
      (cutBulkToAmbient period hPeriod) :=
  (cutBulkToAmbient_contMDiff period hPeriod).mdifferentiable (by simp)

/-- Fiberwise pullback by the genuine manifold derivative of the natural map. -/
def cutBulkAmbientTensorPullback
    (tensor : CovariantTwoTensorField period hPeriod) :
    CutBulkCovariantTwoTensorField period hPeriod :=
  fun point =>
    let derivative := mfderiv cutCollarModelWithCorners coverModelWithCorners
      (cutBulkToAmbient period hPeriod) point
    (derivative.precomp Real).comp
      ((tensor (cutBulkToAmbient period hPeriod point)).comp derivative)

@[simp]
theorem cutBulkAmbientTensorPullback_apply
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (first second : CutBulkTangentFiber period hPeriod point) :
    cutBulkAmbientTensorPullback period hPeriod tensor point first second =
      tensor (cutBulkToAmbient period hPeriod point)
        (mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkToAmbient period hPeriod) point first)
        (mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkToAmbient period hPeriod) point second) := by
  rfl

theorem cutBulkAmbientTensorPullback_symmetric
    (tensor : CovariantTwoTensorField period hPeriod)
    (hTensor : ∀ point first second,
      tensor point first second = tensor point second first)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (first second : CutBulkTangentFiber period hPeriod point) :
    cutBulkAmbientTensorPullback period hPeriod tensor point first second =
      cutBulkAmbientTensorPullback period hPeriod tensor point second first := by
  simp only [cutBulkAmbientTensorPullback_apply]
  exact hTensor _ _ _

end
end P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
end JanusFormal

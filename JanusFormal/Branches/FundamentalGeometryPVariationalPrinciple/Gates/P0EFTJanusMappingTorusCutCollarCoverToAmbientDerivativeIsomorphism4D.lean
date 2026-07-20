import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutCollarProductToAmbientDerivativeIsomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D

/-!
# Differential certificate on the true cut-collar cover
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutCollarCoverToAmbientDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutCollarProductToAmbientDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance boundaryCoverChartedSpace :
    ChartedSpace ThroatCoverModel (BoundaryCover period hPeriod) :=
  fixedThroatCoverChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private def boundaryCoverProductDiffeomorph :
    BoundaryCover period hPeriod ≃ₘ^∞⟮throatCoverModelWithCorners,
      throatCoverModelWithCorners⟯ EquatorialTwoSphere × Real where
  toEquiv := (coverHomeomorphProd
    (orientationDoubleData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ∞
      (coverHomeomorphProd (orientationDoubleData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ∞
      (coverHomeomorphProd (orientationDoubleData period hPeriod))

private def cutCollarCoverProductDiffeomorph :
    (BoundaryCover period hPeriod × CutCollarInterval) ≃ₘ^∞⟮
      cutCollarModelWithCorners, cutCollarModelWithCorners⟯
      ((EquatorialTwoSphere × Real) × CutCollarInterval) :=
  (boundaryCoverProductDiffeomorph period hPeriod).prodCongr
    (Diffeomorph.refl (modelWithCornersEuclideanHalfSpace 1)
      CutCollarInterval ∞)

/-- The collar-cover map expressed through the certified product coordinates. -/
def cutCollarCoverToAmbient
    (parameter : BoundaryCover period hPeriod × CutCollarInterval) :
    EffectiveQuotient period hPeriod :=
  cutCollarProductToAmbient period hPeriod
    (cutCollarCoverProductDiffeomorph period hPeriod parameter)

theorem cutCollarCoverToAmbient_contMDiff :
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (cutCollarCoverToAmbient period hPeriod) :=
  (cutCollarProductToAmbient_contMDiff period hPeriod).comp
    (cutCollarCoverProductDiffeomorph period hPeriod).contMDiff

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarCoverToAmbient_derivative_isomorphism
    (parameter : BoundaryCover period hPeriod × CutCollarInterval) :
    ∃ derivative : TangentSpace cutCollarModelWithCorners parameter ≃L[Real]
        TangentSpace coverModelWithCorners
          (cutCollarCoverToAmbient period hPeriod parameter),
      (derivative : TangentSpace cutCollarModelWithCorners parameter →L[Real]
        TangentSpace coverModelWithCorners
          (cutCollarCoverToAmbient period hPeriod parameter)) =
        mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutCollarCoverToAmbient period hPeriod) parameter := by
  unfold cutCollarCoverToAmbient
  let coordinateDerivative :=
    (cutCollarCoverProductDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) parameter
  let productDerivative :=
    (cutCollarProductToAmbient_derivative_isomorphism period hPeriod
      (cutCollarCoverProductDiffeomorph period hPeriod parameter)).choose
  have hProductDerivative :=
    (cutCollarProductToAmbient_derivative_isomorphism period hPeriod
      (cutCollarCoverProductDiffeomorph period hPeriod parameter)).choose_spec
  let derivative := coordinateDerivative.trans productDerivative
  refine ⟨derivative, ?_⟩
  have hCoordinates :=
    (cutCollarCoverProductDiffeomorph period hPeriod).contMDiff.mdifferentiableAt
      (x := parameter) (by simp)
  have hProduct := (cutCollarProductToAmbient_contMDiff period hPeriod)
    |>.mdifferentiableAt
      (x := cutCollarCoverProductDiffeomorph period hPeriod parameter) (by simp)
  have hComp := mfderiv_comp parameter hProduct hCoordinates
  ext vector
  change productDerivative (coordinateDerivative vector) = _
  rw [show coordinateDerivative vector =
      mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
        (cutCollarCoverProductDiffeomorph period hPeriod) parameter vector by
    exact DFunLike.congr_fun
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (cutCollarCoverProductDiffeomorph period hPeriod) (by simp)) vector,
    show productDerivative
        (mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
          (cutCollarCoverProductDiffeomorph period hPeriod) parameter vector) =
      mfderiv cutCollarModelWithCorners coverModelWithCorners
        (cutCollarProductToAmbient period hPeriod)
        (cutCollarCoverProductDiffeomorph period hPeriod parameter)
        (mfderiv cutCollarModelWithCorners cutCollarModelWithCorners
          (cutCollarCoverProductDiffeomorph period hPeriod) parameter vector) by
    exact DFunLike.congr_fun hProductDerivative _]
  exact DFunLike.congr_fun hComp.symm vector

theorem cutCollarCoverToAmbient_eq_existing
    (parameter : BoundaryCover period hPeriod × CutCollarInterval) :
    cutCollarCoverToAmbient period hPeriod parameter =
      cutBulkToAmbientCollarCover period hPeriod parameter := by
  rfl

end
end P0EFTJanusMappingTorusCutCollarCoverToAmbientDerivativeIsomorphism4D
end JanusFormal

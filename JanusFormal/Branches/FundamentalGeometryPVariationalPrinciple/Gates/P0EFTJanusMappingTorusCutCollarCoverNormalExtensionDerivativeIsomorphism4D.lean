import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D

/-!
# Derivative isomorphism for the cut-collar cover normal extension
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutCollarCoverNormalExtensionDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev BoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

abbrev SignedCutCollarCoordinates := ThroatCoverCoordinates × Real

def signedCutCollarModelWithCorners :
    ModelWithCorners Real SignedCutCollarCoordinates SignedCutCollarCoordinates :=
  throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)

local instance boundaryCoverChartedSpace :
    ChartedSpace ThroatCoverModel (BoundaryCover period hPeriod) :=
  fixedThroatCoverChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance signedCollarChartedSpace :
    ChartedSpace SignedCutCollarCoordinates
      (BoundaryCover period hPeriod × Real) :=
  prodChartedSpace ThroatCoverModel (BoundaryCover period hPeriod) Real Real

/-- Extend only the collar-normal coordinate from `[0,1]` to `ℝ`. -/
def cutCollarCoverNormalExtension :
    BoundaryCover period hPeriod × CutCollarInterval →
      BoundaryCover period hPeriod × Real :=
  Prod.map id Subtype.val

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarCoverNormalExtension_derivative_isomorphism
    (parameter : BoundaryCover period hPeriod × CutCollarInterval) :
    ∃ derivative : TangentSpace cutCollarModelWithCorners parameter ≃L[Real]
        TangentSpace signedCutCollarModelWithCorners
          (cutCollarCoverNormalExtension period hPeriod parameter),
      (derivative : TangentSpace cutCollarModelWithCorners parameter →L[Real]
        TangentSpace signedCutCollarModelWithCorners
          (cutCollarCoverNormalExtension period hPeriod parameter)) =
        mfderiv cutCollarModelWithCorners signedCutCollarModelWithCorners
          (cutCollarCoverNormalExtension period hPeriod) parameter := by
  unfold cutCollarCoverNormalExtension
  let boundaryDiffeomorphism :=
    Diffeomorph.refl throatCoverModelWithCorners
      (BoundaryCover period hPeriod) ∞
  let boundaryDerivative :=
    boundaryDiffeomorphism.mfderivToContinuousLinearEquiv (by simp) parameter.1
  let normalDerivative := cutCollarNormalDerivativeEquiv parameter.2
  let normalDerivativeModel : EuclideanSpace Real (Fin 1) ≃L[Real] Real := by
    exact normalDerivative
  let productDerivativeModel :=
    boundaryDerivative.prodCongr normalDerivativeModel
  let productDerivative : TangentSpace cutCollarModelWithCorners parameter ≃L[Real]
      TangentSpace signedCutCollarModelWithCorners
        (Prod.map id (Subtype.val : CutCollarInterval → Real) parameter) := by
    exact productDerivativeModel
  refine ⟨productDerivative, ?_⟩
  have hNormal : MDifferentiableAt (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf Real Real)
      (Subtype.val : CutCollarInterval → Real) parameter.2 :=
    (contMDiff_subtype_coe_Icc (n := ∞)).mdifferentiable
      (by simp) parameter.2
  calc
    (productDerivative : TangentSpace cutCollarModelWithCorners parameter →L[Real]
        TangentSpace signedCutCollarModelWithCorners
          (Prod.map id (Subtype.val : CutCollarInterval → Real) parameter)) =
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners id
          parameter.1).prodMap
          (mfderiv (modelWithCornersEuclideanHalfSpace 1)
            (modelWithCornersSelf Real Real)
            (Subtype.val : CutCollarInterval → Real) parameter.2) := by
      ext ⟨boundaryVector, normalVector⟩
      change (boundaryDerivative boundaryVector,
        normalDerivativeModel normalVector) = _
      rw [show boundaryDerivative boundaryVector =
          mfderiv throatCoverModelWithCorners throatCoverModelWithCorners id
            parameter.1 boundaryVector by
        exact DFunLike.congr_fun
          (Diffeomorph.mfderivToContinuousLinearEquiv_coe
            boundaryDiffeomorphism (by simp)) boundaryVector,
        show normalDerivativeModel normalVector =
          mfderiv (modelWithCornersEuclideanHalfSpace 1)
            (modelWithCornersSelf Real Real)
            (Subtype.val : CutCollarInterval → Real) parameter.2 normalVector by
        exact DFunLike.congr_fun
          (cutCollarNormalDerivativeEquiv_coe parameter.2) normalVector]
      rfl
    _ = mfderiv cutCollarModelWithCorners signedCutCollarModelWithCorners
        (Prod.map id (Subtype.val : CutCollarInterval → Real)) parameter :=
      (mfderiv_prodMap mdifferentiableAt_id hNormal).symm

end
end P0EFTJanusMappingTorusCutCollarCoverNormalExtensionDerivativeIsomorphism4D
end JanusFormal

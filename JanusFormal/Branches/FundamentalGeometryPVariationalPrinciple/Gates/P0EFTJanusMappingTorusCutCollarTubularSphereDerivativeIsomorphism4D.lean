import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutCollarTubularNormalLift4D

/-!
# Differential certificate for the spherical tubular cut-collar map
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutCollarTubularSphereDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusMappingTorusCutCollarTubularNormalLift4D

/-- The spherical part of the collar attachment, valued in the tubular band. -/
def cutCollarTubularSphereMap
    (parameter : EquatorialTwoSphere × CutCollarInterval) :
    equatorialSphericalBandOpen :=
  equatorialTubularSmoothMap (cutCollarTubularParameterLift parameter)

theorem cutCollarTubularSphereMap_contMDiff :
    ContMDiff ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
      (𝓡 3) ∞ cutCollarTubularSphereMap :=
  equatorialTubularDiffeomorph.contMDiff.comp
    cutCollarTubularParameterLift_contMDiff

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarTubularSphereMap_derivative_isomorphism
    (parameter : EquatorialTwoSphere × CutCollarInterval) :
    ∃ derivative :
        TangentSpace ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) parameter ≃L[Real]
          TangentSpace (𝓡 3) (cutCollarTubularSphereMap parameter),
      (derivative :
          TangentSpace ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) parameter →L[Real]
            TangentSpace (𝓡 3) (cutCollarTubularSphereMap parameter)) =
        mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
          (𝓡 3) cutCollarTubularSphereMap parameter := by
  unfold cutCollarTubularSphereMap
  let liftDerivative :=
    (cutCollarTubularParameterLift_derivative_isomorphism parameter).choose
  have hLiftDerivative :=
    (cutCollarTubularParameterLift_derivative_isomorphism parameter).choose_spec
  let tubularDerivative :=
    equatorialTubularDiffeomorph.mfderivToContinuousLinearEquiv (by simp)
      (cutCollarTubularParameterLift parameter)
  let derivative := liftDerivative.trans tubularDerivative
  refine ⟨derivative, ?_⟩
  have hLift := cutCollarTubularParameterLift_contMDiff.mdifferentiableAt
    (x := parameter) (by simp)
  have hTubular := equatorialTubularDiffeomorph.contMDiff.mdifferentiableAt
    (x := cutCollarTubularParameterLift parameter) (by simp)
  have hComp := mfderiv_comp parameter hTubular hLift
  ext vector
  change tubularDerivative (liftDerivative vector) = _
  rw [show liftDerivative vector =
      mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
        ((𝓡 2).prod (modelWithCornersSelf Real Real))
        cutCollarTubularParameterLift parameter vector by
    exact DFunLike.congr_fun hLiftDerivative vector,
    show tubularDerivative
        (mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
          ((𝓡 2).prod (modelWithCornersSelf Real Real))
          cutCollarTubularParameterLift parameter vector) =
      mfderiv ((𝓡 2).prod (modelWithCornersSelf Real Real)) (𝓡 3)
        equatorialTubularSmoothMap (cutCollarTubularParameterLift parameter)
        (mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
          ((𝓡 2).prod (modelWithCornersSelf Real Real))
          cutCollarTubularParameterLift parameter vector) by
    exact DFunLike.congr_fun
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe
        equatorialTubularDiffeomorph (by simp)) _]
  exact DFunLike.congr_fun hComp.symm vector

end
end P0EFTJanusMappingTorusCutCollarTubularSphereDerivativeIsomorphism4D
end JanusFormal

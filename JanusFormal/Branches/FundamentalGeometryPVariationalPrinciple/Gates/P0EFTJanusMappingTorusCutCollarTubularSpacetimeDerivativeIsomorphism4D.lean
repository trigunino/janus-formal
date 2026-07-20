import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutCollarTubularSphereDerivativeIsomorphism4D

/-!
# Spacetime tubular differential certificate on cut-collar coordinates
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutCollarTubularSpacetimeDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusMappingTorusCutCollarTubularSphereDerivativeIsomorphism4D

/-- Reassociate `(sphere, time, normal)` as `(sphere, normal, time)`. -/
def cutCollarTimeReassociation :
    ((EquatorialTwoSphere × Real) × CutCollarInterval) ≃ₘ^∞⟮
      (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
        (modelWithCornersEuclideanHalfSpace 1)),
      (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
        (modelWithCornersSelf Real Real))⟯
      ((EquatorialTwoSphere × CutCollarInterval) × Real) where
  toFun parameter := ((parameter.1.1, parameter.2), parameter.1.2)
  invFun parameter := ((parameter.1.1, parameter.2), parameter.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)

@[simp] theorem cutCollarTimeReassociation_apply
    (parameter : (EquatorialTwoSphere × Real) × CutCollarInterval) :
    cutCollarTimeReassociation parameter =
      ((parameter.1.1, parameter.2), parameter.1.2) := rfl

/-- Tubular spherical attachment with the time coordinate unchanged. -/
def cutCollarTubularSpacetimeMap
    (parameter : (EquatorialTwoSphere × Real) × CutCollarInterval) :
    equatorialSphericalBandOpen × Real :=
  Prod.map cutCollarTubularSphereMap (id : Real → Real)
    (cutCollarTimeReassociation parameter)

theorem cutCollarTubularSpacetimeMap_contMDiff :
    ContMDiff
      (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
        (modelWithCornersEuclideanHalfSpace 1))
      ((𝓡 3).prod (modelWithCornersSelf Real Real)) ∞
      cutCollarTubularSpacetimeMap := by
  have hProduct := cutCollarTubularSphereMap_contMDiff.prodMap
    (contMDiff_id : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ (id : Real → Real))
  exact (hProduct.comp cutCollarTimeReassociation.contMDiff).congr fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarTubularSpacetimeMap_derivative_isomorphism
    (parameter : (EquatorialTwoSphere × Real) × CutCollarInterval) :
    ∃ derivative :
        TangentSpace
          (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
            (modelWithCornersEuclideanHalfSpace 1)) parameter ≃L[Real]
          TangentSpace ((𝓡 3).prod (modelWithCornersSelf Real Real))
            (cutCollarTubularSpacetimeMap parameter),
      (derivative :
          TangentSpace
            (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
              (modelWithCornersEuclideanHalfSpace 1)) parameter →L[Real]
            TangentSpace ((𝓡 3).prod (modelWithCornersSelf Real Real))
              (cutCollarTubularSpacetimeMap parameter)) =
        mfderiv
          (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
            (modelWithCornersEuclideanHalfSpace 1))
          ((𝓡 3).prod (modelWithCornersSelf Real Real))
          cutCollarTubularSpacetimeMap parameter := by
  unfold cutCollarTubularSpacetimeMap
  let reassociationDerivative :=
    cutCollarTimeReassociation.mfderivToContinuousLinearEquiv (by simp) parameter
  let sphereDerivative :=
    (cutCollarTubularSphereMap_derivative_isomorphism
      (cutCollarTimeReassociation parameter).1).choose
  have hSphereDerivative :=
    (cutCollarTubularSphereMap_derivative_isomorphism
      (cutCollarTimeReassociation parameter).1).choose_spec
  let timeDiffeomorphism :=
    Diffeomorph.refl (modelWithCornersSelf Real Real) Real ∞
  let timeDerivative :=
    timeDiffeomorphism.mfderivToContinuousLinearEquiv (by simp)
      (cutCollarTimeReassociation parameter).2
  let productDerivative := sphereDerivative.prodCongr timeDerivative
  let productDerivativeAt :
      TangentSpace
        (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
          (modelWithCornersSelf Real Real))
          (cutCollarTimeReassociation parameter) ≃L[Real]
        TangentSpace ((𝓡 3).prod (modelWithCornersSelf Real Real))
          (Prod.map cutCollarTubularSphereMap (id : Real → Real)
            (cutCollarTimeReassociation parameter)) := by
    exact productDerivative
  let derivative := reassociationDerivative.trans productDerivativeAt
  refine ⟨derivative, ?_⟩
  have hSphere := cutCollarTubularSphereMap_contMDiff.mdifferentiableAt
    (x := (cutCollarTimeReassociation parameter).1) (by simp)
  have hTime : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) (id : Real → Real)
        (cutCollarTimeReassociation parameter).2 :=
    mdifferentiableAt_id
  have hProduct := mfderiv_prodMap hSphere hTime
  have hReassociation := cutCollarTimeReassociation.contMDiff.mdifferentiableAt
    (x := parameter) (by simp)
  have hOuter : MDifferentiableAt
      (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
        (modelWithCornersSelf Real Real))
      ((𝓡 3).prod (modelWithCornersSelf Real Real))
      (Prod.map cutCollarTubularSphereMap (id : Real → Real))
        (cutCollarTimeReassociation parameter) :=
    (cutCollarTubularSphereMap_contMDiff.prodMap
      (contMDiff_id : ContMDiff (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) ∞ (id : Real → Real))).mdifferentiableAt
        (by simp)
  have hComp := mfderiv_comp parameter hOuter hReassociation
  have hProductDerivative :
      (productDerivativeAt :
        TangentSpace
          (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
            (modelWithCornersSelf Real Real))
            (cutCollarTimeReassociation parameter) →L[Real]
          TangentSpace ((𝓡 3).prod (modelWithCornersSelf Real Real))
            (Prod.map cutCollarTubularSphereMap (id : Real → Real)
              (cutCollarTimeReassociation parameter))) =
        mfderiv
          (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
            (modelWithCornersSelf Real Real))
          ((𝓡 3).prod (modelWithCornersSelf Real Real))
          (Prod.map cutCollarTubularSphereMap (id : Real → Real))
            (cutCollarTimeReassociation parameter) := by
    calc
      (productDerivativeAt :
          TangentSpace
            (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
              (modelWithCornersSelf Real Real))
              (cutCollarTimeReassociation parameter) →L[Real]
            TangentSpace ((𝓡 3).prod (modelWithCornersSelf Real Real))
              (Prod.map cutCollarTubularSphereMap (id : Real → Real)
                (cutCollarTimeReassociation parameter))) =
          (mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) (𝓡 3)
            cutCollarTubularSphereMap
              (cutCollarTimeReassociation parameter).1).prodMap
            (mfderiv (modelWithCornersSelf Real Real)
              (modelWithCornersSelf Real Real) id
                (cutCollarTimeReassociation parameter).2) := by
        ext ⟨sphereVector, timeVector⟩
        change (sphereDerivative sphereVector, timeDerivative timeVector) = _
        rw [show sphereDerivative sphereVector =
            mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) (𝓡 3)
              cutCollarTubularSphereMap
                (cutCollarTimeReassociation parameter).1 sphereVector by
          exact DFunLike.congr_fun hSphereDerivative sphereVector,
          show timeDerivative timeVector =
            mfderiv (modelWithCornersSelf Real Real)
              (modelWithCornersSelf Real Real) id
                (cutCollarTimeReassociation parameter).2 timeVector by
          exact DFunLike.congr_fun
            (Diffeomorph.mfderivToContinuousLinearEquiv_coe
              timeDiffeomorphism (by simp)) timeVector]
        rfl
      _ = mfderiv
          (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
            (modelWithCornersSelf Real Real))
          ((𝓡 3).prod (modelWithCornersSelf Real Real))
          (Prod.map cutCollarTubularSphereMap (id : Real → Real))
            (cutCollarTimeReassociation parameter) :=
        hProduct.symm
  ext vector
  change productDerivativeAt (reassociationDerivative vector) = _
  rw [show reassociationDerivative vector =
      mfderiv
        (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
          (modelWithCornersEuclideanHalfSpace 1))
        (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
          (modelWithCornersSelf Real Real))
        cutCollarTimeReassociation parameter vector by
    exact DFunLike.congr_fun
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe
        cutCollarTimeReassociation (by simp)) vector]
  calc
    productDerivativeAt
        (mfderiv
          (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
            (modelWithCornersEuclideanHalfSpace 1))
          (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
            (modelWithCornersSelf Real Real))
          cutCollarTimeReassociation parameter vector) =
      mfderiv
          (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
            (modelWithCornersSelf Real Real))
          ((𝓡 3).prod (modelWithCornersSelf Real Real))
          (Prod.map cutCollarTubularSphereMap (id : Real → Real))
          (cutCollarTimeReassociation parameter)
          (mfderiv
            (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
              (modelWithCornersEuclideanHalfSpace 1))
            (((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)).prod
              (modelWithCornersSelf Real Real))
            cutCollarTimeReassociation parameter vector) :=
      DFunLike.congr_fun hProductDerivative _
    _ = mfderiv
        (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
          (modelWithCornersEuclideanHalfSpace 1))
        ((𝓡 3).prod (modelWithCornersSelf Real Real))
        (fun current => Prod.map cutCollarTubularSphereMap (id : Real → Real)
          (cutCollarTimeReassociation current)) parameter vector :=
      DFunLike.congr_fun hComp.symm vector

end
end P0EFTJanusMappingTorusCutCollarTubularSpacetimeDerivativeIsomorphism4D
end JanusFormal

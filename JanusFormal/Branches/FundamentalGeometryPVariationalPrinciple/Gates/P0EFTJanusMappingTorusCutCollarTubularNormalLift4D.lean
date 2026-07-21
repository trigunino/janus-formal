import Mathlib.Analysis.Real.Pi.Bounds
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutCollarCoverNormalExtensionDerivativeIsomorphism4D

/-!
# Tubular-normal lift of the finite cut collar

The interval `[0,1]` lies in the normal domain `(-π/2, π/2)` of the
equatorial tubular diffeomorphism.  This gate packages that inclusion smoothly.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutCollarTubularNormalLift4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D

/-- The finite collar normal, viewed in the tubular normal open interval. -/
def cutCollarTubularNormalLift
    (normal : CutCollarInterval) : equatorialTubularNormalOpen :=
  ⟨normal.1, by
    constructor
    · nlinarith [Real.pi_pos, normal.2.1]
    · nlinarith [Real.pi_gt_three, normal.2.2]⟩

@[simp] theorem cutCollarTubularNormalLift_coe
    (normal : CutCollarInterval) :
    (cutCollarTubularNormalLift normal : Real) = normal := rfl

theorem cutCollarTubularNormalLift_contMDiff :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf Real Real) ∞ cutCollarTubularNormalLift := by
  rw [← ContMDiff.subtypeVal_comp_iff equatorialTubularNormalOpen]
  exact contMDiff_subtype_coe_Icc

private def tubularNormalOpenSubtypePartialDiffeomorph
    (base : equatorialTubularNormalOpen) :
    PartialDiffeomorph (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) equatorialTubularNormalOpen Real ∞ := by
  letI : Nonempty equatorialTubularNormalOpen := ⟨base⟩
  exact
    { __ := equatorialTubularNormalOpen.2.isOpenEmbedding_subtypeVal
        |>.toOpenPartialHomeomorph Subtype.val
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        intro point hPoint
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff equatorialTubularNormalOpen]
        apply contMDiffWithinAt_id.congr_of_mem _ hPoint
        intro target hTarget
        exact equatorialTubularNormalOpen.2.isOpenEmbedding_subtypeVal
          |>.toOpenPartialHomeomorph_right_inv Subtype.val hTarget }

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarTubularNormalLift_derivative_isomorphism
    (normal : CutCollarInterval) :
    ∃ derivative : TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal ≃L[Real]
        TangentSpace (modelWithCornersSelf Real Real)
          (cutCollarTubularNormalLift normal),
      (derivative : TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal →L[Real]
        TangentSpace (modelWithCornersSelf Real Real)
          (cutCollarTubularNormalLift normal)) =
        mfderiv (modelWithCornersEuclideanHalfSpace 1)
          (modelWithCornersSelf Real Real) cutCollarTubularNormalLift normal := by
  let liftPoint := cutCollarTubularNormalLift normal
  let openPartial := tubularNormalOpenSubtypePartialDiffeomorph liftPoint
  have hOpenLocal : IsLocalDiffeomorphAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞
      (Subtype.val : equatorialTubularNormalOpen → Real) liftPoint := by
    apply openPartial.isLocalDiffeomorphAt _ _ _
    change liftPoint ∈ Set.univ
    simp
  let openDerivative :=
    hOpenLocal.mfderivToContinuousLinearEquiv (by simp)
  let normalDerivative := cutCollarNormalDerivativeEquiv normal
  let derivative := normalDerivative.trans openDerivative.symm
  refine ⟨derivative, ?_⟩
  have hLift := cutCollarTubularNormalLift_contMDiff.mdifferentiableAt
    (x := normal) (by simp)
  have hOpen := hOpenLocal.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp normal hOpen hLift
  rw [show (Subtype.val : equatorialTubularNormalOpen → Real) ∘
      cutCollarTubularNormalLift =
      (Subtype.val : CutCollarInterval → Real) by rfl,
    ← cutCollarNormalDerivativeEquiv_coe normal,
    ← hOpenLocal.mfderivToContinuousLinearEquiv_coe (by simp)] at hComp
  ext vector
  apply openDerivative.injective
  change openDerivative (openDerivative.symm (normalDerivative vector)) = _
  rw [openDerivative.apply_symm_apply]
  change normalDerivative vector =
    openDerivative
      (mfderiv (modelWithCornersEuclideanHalfSpace 1)
        (modelWithCornersSelf Real Real) cutCollarTubularNormalLift normal vector)
  exact DFunLike.congr_fun hComp vector

/-- Product lift used before applying the equatorial tubular diffeomorphism. -/
def cutCollarTubularParameterLift
    (parameter : EquatorialTwoSphere × CutCollarInterval) :
    EquatorialTwoSphere × equatorialTubularNormalOpen :=
  (parameter.1, cutCollarTubularNormalLift parameter.2)

theorem cutCollarTubularParameterLift_contMDiff :
    ContMDiff ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
      ((𝓡 2).prod (modelWithCornersSelf Real Real)) ∞
      cutCollarTubularParameterLift :=
  contMDiff_fst.prodMk
    (cutCollarTubularNormalLift_contMDiff.comp contMDiff_snd)

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarTubularParameterLift_derivative_isomorphism
    (parameter : EquatorialTwoSphere × CutCollarInterval) :
    ∃ derivative :
        TangentSpace ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) parameter ≃L[Real]
          TangentSpace ((𝓡 2).prod (modelWithCornersSelf Real Real))
            (cutCollarTubularParameterLift parameter),
      (derivative :
          TangentSpace ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) parameter →L[Real]
            TangentSpace ((𝓡 2).prod (modelWithCornersSelf Real Real))
              (cutCollarTubularParameterLift parameter)) =
        mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
          ((𝓡 2).prod (modelWithCornersSelf Real Real))
          cutCollarTubularParameterLift parameter := by
  unfold cutCollarTubularParameterLift
  let sphereDiffeomorphism := Diffeomorph.refl (𝓡 2) EquatorialTwoSphere ∞
  let sphereDerivative :=
    sphereDiffeomorphism.mfderivToContinuousLinearEquiv (by simp) parameter.1
  let normalDerivative :=
    (cutCollarTubularNormalLift_derivative_isomorphism parameter.2).choose
  have hNormalDerivative :=
    (cutCollarTubularNormalLift_derivative_isomorphism parameter.2).choose_spec
  let derivativeModel := sphereDerivative.prodCongr normalDerivative
  let derivative :
      TangentSpace ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) parameter ≃L[Real]
        TangentSpace ((𝓡 2).prod (modelWithCornersSelf Real Real))
          (Prod.map id cutCollarTubularNormalLift parameter) := by
    exact derivativeModel
  refine ⟨derivative, ?_⟩
  have hNormal := cutCollarTubularNormalLift_contMDiff.mdifferentiableAt
    (x := parameter.2) (by simp)
  calc
    (derivative :
        TangentSpace ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1)) parameter →L[Real]
          TangentSpace ((𝓡 2).prod (modelWithCornersSelf Real Real))
            (Prod.map id cutCollarTubularNormalLift parameter)) =
        (mfderiv (𝓡 2) (𝓡 2) id parameter.1).prodMap
          (mfderiv (modelWithCornersEuclideanHalfSpace 1)
            (modelWithCornersSelf Real Real)
            cutCollarTubularNormalLift parameter.2) := by
      ext ⟨sphereVector, normalVector⟩
      change (sphereDerivative sphereVector, normalDerivative normalVector) = _
      rw [show sphereDerivative sphereVector =
          mfderiv (𝓡 2) (𝓡 2) id parameter.1 sphereVector by
        exact DFunLike.congr_fun
          (Diffeomorph.mfderivToContinuousLinearEquiv_coe
            sphereDiffeomorphism (by simp)) sphereVector,
        show normalDerivative normalVector =
          mfderiv (modelWithCornersEuclideanHalfSpace 1)
            (modelWithCornersSelf Real Real)
            cutCollarTubularNormalLift parameter.2 normalVector by
        exact DFunLike.congr_fun hNormalDerivative normalVector]
      rfl
    _ = mfderiv ((𝓡 2).prod (modelWithCornersEuclideanHalfSpace 1))
        ((𝓡 2).prod (modelWithCornersSelf Real Real))
        (Prod.map id cutCollarTubularNormalLift) parameter :=
      (mfderiv_prodMap mdifferentiableAt_id hNormal).symm

@[simp] theorem equatorialTubularSmoothMap_cutCollarTubularParameterLift
    (parameter : EquatorialTwoSphere × CutCollarInterval) :
    equatorialTubularSmoothMap (cutCollarTubularParameterLift parameter) =
      ⟨equatorialLatitude parameter.1 parameter.2.1, by
        change |Real.sin parameter.2.1| < 1
        rw [abs_lt]
        have hCos := Real.cos_pos_of_mem_Ioo
          (cutCollarTubularNormalLift parameter.2).2
        have hCosSq : 0 < Real.cos parameter.2.1 ^ 2 := sq_pos_of_pos hCos
        constructor <;> nlinarith [Real.sin_sq_add_cos_sq parameter.2.1]⟩ := rfl

end
end P0EFTJanusMappingTorusCutCollarTubularNormalLift4D
end JanusFormal

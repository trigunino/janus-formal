import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalCapDerivativeIsomorphism4D

/-!
# Normal derivative isomorphism for the cut collar
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D

set_option backward.isDefEq.respectTransparency false in
/-- The tangent map of the collar-normal inclusion is the identity, including
at the true boundary `0`. -/
def cutCollarNormalDerivativeEquiv (normal : CutCollarInterval) :
    TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal ≃L[Real]
      TangentSpace (modelWithCornersSelf Real Real) normal.1 := by
  let sourceCoordinates := VectorBundle.continuousLinearEquivAt Real
    (EuclideanSpace Real (Fin 1))
    (TangentSpace (modelWithCornersEuclideanHalfSpace 1)) normal
  let targetCoordinates := VectorBundle.continuousLinearEquivAt Real Real
    (TangentSpace (modelWithCornersSelf Real Real)) normal.1
  letI : FiniteDimensional Real
      (TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal) :=
    sourceCoordinates.toLinearEquiv.symm.finiteDimensional
  letI : FiniteDimensional Real
      (TangentSpace (modelWithCornersSelf Real Real) normal.1) :=
    targetCoordinates.toLinearEquiv.symm.finiteDimensional
  let derivative := mfderiv (modelWithCornersEuclideanHalfSpace 1)
    (modelWithCornersSelf Real Real)
    (Subtype.val : CutCollarInterval → Real) normal
  have hTargetOne : (1 : TangentSpace
      (modelWithCornersSelf Real Real) normal.1) ≠ 0 := by
    change (1 : Real) ≠ 0
    exact one_ne_zero
  have hDerivativeNonzero : (derivative :
      TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal →ₗ[Real]
        TangentSpace (modelWithCornersSelf Real Real) normal.1) ≠ 0 := by
    intro hZero
    have hApply := DFunLike.congr_fun hZero
      (1 : TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal)
    change mfderiv (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf Real Real)
      (Subtype.val : CutCollarInterval → Real) normal 1 = 0 at hApply
    rw [mfderiv_subtype_coe_Icc_one] at hApply
    exact hTargetOne hApply
  have hTargetFinrank : Module.finrank Real
      (TangentSpace (modelWithCornersSelf Real Real) normal.1) = 1 := by
    rw [targetCoordinates.toLinearEquiv.finrank_eq]
    simp
  have hSurjective : Function.Surjective derivative :=
    surjective_of_nonzero_of_finrank_eq_one hTargetFinrank hDerivativeNonzero
  have hFinrank : Module.finrank Real
      (TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal) =
      Module.finrank Real
        (TangentSpace (modelWithCornersSelf Real Real) normal.1) := by
    rw [sourceCoordinates.toLinearEquiv.finrank_eq,
      targetCoordinates.toLinearEquiv.finrank_eq]
    simp
  have hInjective : Function.Injective derivative :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hFinrank).2
      hSurjective
  let coordinateDerivative : EuclideanSpace Real (Fin 1) →L[Real] Real :=
    (targetCoordinates : _ →L[Real] Real).comp
      (derivative.comp (sourceCoordinates.symm : _ →L[Real] _))
  have hCoordinateInjective : Function.Injective coordinateDerivative :=
    targetCoordinates.injective.comp
      (hInjective.comp sourceCoordinates.symm.injective)
  have hCoordinateSurjective : Function.Surjective coordinateDerivative :=
    targetCoordinates.surjective.comp
      (hSurjective.comp sourceCoordinates.symm.surjective)
  let coordinateEquiv := ContinuousLinearEquiv.ofBijective coordinateDerivative
    (LinearMap.ker_eq_bot.mpr hCoordinateInjective)
    (LinearMap.range_eq_top.mpr hCoordinateSurjective)
  exact sourceCoordinates.trans (coordinateEquiv.trans targetCoordinates.symm)

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarNormalDerivativeEquiv_coe (normal : CutCollarInterval) :
    (cutCollarNormalDerivativeEquiv normal :
      TangentSpace (modelWithCornersEuclideanHalfSpace 1) normal →L[Real]
        TangentSpace (modelWithCornersSelf Real Real) normal.1) =
      mfderiv (modelWithCornersEuclideanHalfSpace 1)
        (modelWithCornersSelf Real Real)
        (Subtype.val : CutCollarInterval → Real) normal := by
  apply ContinuousLinearMap.ext
  intro vector
  let sourceCoordinates := VectorBundle.continuousLinearEquivAt Real
    (EuclideanSpace Real (Fin 1))
    (TangentSpace (modelWithCornersEuclideanHalfSpace 1)) normal
  let targetCoordinates := VectorBundle.continuousLinearEquivAt Real Real
    (TangentSpace (modelWithCornersSelf Real Real)) normal.1
  change targetCoordinates.symm
      (targetCoordinates
        (mfderiv (modelWithCornersEuclideanHalfSpace 1)
          (modelWithCornersSelf Real Real)
          (Subtype.val : CutCollarInterval → Real) normal
          (sourceCoordinates.symm (sourceCoordinates vector)))) =
    mfderiv (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf Real Real)
      (Subtype.val : CutCollarInterval → Real) normal vector
  simp

end
end P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D
end JanusFormal

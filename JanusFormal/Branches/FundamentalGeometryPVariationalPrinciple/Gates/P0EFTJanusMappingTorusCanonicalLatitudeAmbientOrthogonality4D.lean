import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

/-!
# Ambient orthogonality of the canonical latitude collar

The ambient derivative of every sphere tangent is orthogonal to the radial
vector.  This is the geometric input needed to identify the latitude
coordinate differential with the metric normal covector away from the throat.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeAmbientOrthogonality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D

/-- Unit vector in the ambient latitude coordinate. -/
def ambientLatitudeAxis : EuclideanR4 :=
  EuclideanSpace.single (0 : Fin 4) 1

@[simp]
theorem sphereAmbientMap_equatorialLatitude_apply
    (point : EquatorialTwoSphere) (normal : Real) (index : Fin 4) :
    sphereAmbientMap (equatorialLatitude point normal) index =
      Fin.cases (Real.sin normal)
        (fun tail : Fin 3 => Real.cos normal * point.1 tail.succ) index := by
  rfl

/-- Away from the poles, the latitude velocity is a linear combination of
the latitude axis and the sphere radius. -/
theorem latitudeAmbientVelocity_eq_axis_sub_radius
    (point : EquatorialTwoSphere) (normal : Real)
    (hCos : Real.cos normal ≠ 0) :
    latitudeAmbientVelocity point normal =
      (Real.cos normal)⁻¹ • ambientLatitudeAxis -
        (Real.sin normal * (Real.cos normal)⁻¹) •
          sphereAmbientMap (equatorialLatitude point normal) := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · simp [latitudeAmbientVelocity, ambientLatitudeAxis]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq normal]
  · simp [latitudeAmbientVelocity, ambientLatitudeAxis]
    field_simp

/-- The ambient derivative of a sphere tangent is orthogonal to the radius. -/
theorem sphereAmbientMap_inner_mfderiv_zero
    (point : UnitThreeSphere)
    (tangent : TangentSpace (𝓡 3) point) :
    inner Real (sphereAmbientMap point)
      (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap point tangent) = 0 := by
  let standard := unitThreeSphereHomeomorph point
  have hInclusion : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : Metric.sphere (0 : EuclideanR4) 1 → EuclideanR4) standard :=
    (contMDiff_coe_sphere (n := 3)).mdifferentiableAt one_ne_zero
  have hHomeomorph : MDifferentiableAt (𝓡 3) (𝓡 3)
      unitThreeSphereHomeomorph point :=
    (chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
      unitThreeSphereHomeomorph).mdifferentiableAt (by simp)
  let derivative : TangentSpace (𝓡 3) standard →L[Real] EuclideanR4 :=
    mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : Metric.sphere (0 : EuclideanR4) 1 → EuclideanR4) standard
  let standardTangent :=
    mfderiv (𝓡 3) (𝓡 3) unitThreeSphereHomeomorph point tangent
  have hFactor :
      mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap point =
        derivative.comp
          (mfderiv (𝓡 3) (𝓡 3) unitThreeSphereHomeomorph point) := by
    change mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
        (((↑) : Metric.sphere (0 : EuclideanR4) 1 → EuclideanR4) ∘
          unitThreeSphereHomeomorph) point = _
    exact mfderiv_comp point hInclusion hHomeomorph
  have hRange :
      derivative standardTangent ∈
        (Real ∙ (standard : EuclideanR4))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := 3) standard]
    exact ⟨_, rfl⟩
  have hOrthogonal :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hRange
  have hApply := DFunLike.congr_fun hFactor tangent
  calc
    inner Real (sphereAmbientMap point)
        (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
          sphereAmbientMap point tangent) =
      inner Real (standard : EuclideanR4)
        (derivative standardTangent) := by
            rw [hApply]
            rfl
    _ = 0 := hOrthogonal

@[simp]
theorem sphereLatitudeCoordinate_equatorialLatitude
    (point : EquatorialTwoSphere) (normal : Real) :
    sphereLatitudeCoordinate (equatorialLatitude point normal) =
      Real.sin normal := by
  exact sphereAmbientMap_equatorialLatitude_apply point normal 0

/-- Moving the equatorial base point at fixed latitude has zero derivative in
the ambient latitude-axis direction. -/
theorem sphereAmbientDerivative_fixedLatitude_latitudeCoordinate_zero
    (point : EquatorialTwoSphere) (normal : Real)
    (tangent : TangentSpace (𝓡 2) point) :
    (show EuclideanR4 from
      mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
        (equatorialLatitude point normal)
        (mfderiv (𝓡 2) (𝓡 3) (fun source : EquatorialTwoSphere =>
          equatorialLatitude source normal) point tangent)) (0 : Fin 4) = 0 := by
  let latitudeMap : EquatorialTwoSphere → UnitThreeSphere :=
    fun source => equatorialLatitude source normal
  have hLatitudeMap : MDifferentiableAt (𝓡 2) (𝓡 3)
      latitudeMap point :=
    (equatorialLatitude_joint_contMDiff.comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
  have hLatitudeCoordinate : MDifferentiableAt (𝓡 3) 𝓘(Real, Real)
      sphereLatitudeCoordinate (latitudeMap point) :=
    sphereLatitudeCoordinate_contMDiff.mdifferentiableAt (by simp)
  have hAlong := mfderiv_comp_apply point hLatitudeCoordinate hLatitudeMap tangent
  have hConstant : sphereLatitudeCoordinate ∘ latitudeMap =
      fun _ : EquatorialTwoSphere => Real.sin normal := by
    funext source
    exact sphereLatitudeCoordinate_equatorialLatitude source normal
  rw [hConstant, mfderiv_const] at hAlong
  have hAmbient : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      sphereAmbientMap (latitudeMap point) :=
    sphereAmbientMap_contMDiff.mdifferentiableAt (by simp)
  have hProjection : MDifferentiableAt 𝓘(Real, EuclideanR4) 𝓘(Real, Real)
      (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 4))
      (sphereAmbientMap (latitudeMap point)) :=
    (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 4)).differentiableAt.mdifferentiableAt
  let latitudeTangent := mfderiv (𝓡 2) (𝓡 3) latitudeMap point tangent
  have hCoordinateDerivative :
      mfderiv (𝓡 3) 𝓘(Real, Real) sphereLatitudeCoordinate
          (latitudeMap point) latitudeTangent =
        (show EuclideanR4 from
          mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
            (latitudeMap point) latitudeTangent) (0 : Fin 4) := by
    have hChain := mfderiv_comp_apply (latitudeMap point)
      hProjection hAmbient latitudeTangent
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
    convert hChain using 1 <;> rfl
  change (0 : Real) = mfderiv (𝓡 3) 𝓘(Real, Real)
    sphereLatitudeCoordinate (latitudeMap point) latitudeTangent at hAlong
  exact hCoordinateDerivative.symm.trans hAlong.symm

/-- At every nonpolar latitude, the latitude velocity is orthogonal to every
base-sphere tangent transported at fixed latitude. -/
theorem latitudeAmbientVelocity_inner_fixedLatitudeDerivative_zero
    (point : EquatorialTwoSphere) (normal : Real)
    (hCos : Real.cos normal ≠ 0)
    (tangent : TangentSpace (𝓡 2) point) :
    inner Real (latitudeAmbientVelocity point normal)
      (show EuclideanR4 from
        mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
          (equatorialLatitude point normal)
          (mfderiv (𝓡 2) (𝓡 3) (fun source : EquatorialTwoSphere =>
            equatorialLatitude source normal) point tangent)) = 0 := by
  let latitudeTangent :=
    mfderiv (𝓡 2) (𝓡 3) (fun source : EquatorialTwoSphere =>
      equatorialLatitude source normal) point tangent
  let ambientTangent : EuclideanR4 :=
    mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
      (equatorialLatitude point normal) latitudeTangent
  have hAxis : inner Real ambientLatitudeAxis ambientTangent = 0 := by
    simpa [ambientLatitudeAxis, EuclideanSpace.inner_single_left] using
      sphereAmbientDerivative_fixedLatitude_latitudeCoordinate_zero
        point normal tangent
  have hRadius : inner Real
      (sphereAmbientMap (equatorialLatitude point normal)) ambientTangent = 0 :=
    sphereAmbientMap_inner_mfderiv_zero
      (equatorialLatitude point normal) latitudeTangent
  rw [latitudeAmbientVelocity_eq_axis_sub_radius point normal hCos,
    inner_sub_left, inner_smul_left, inner_smul_left, hAxis, hRadius]
  simp

end

end P0EFTJanusMappingTorusCanonicalLatitudeAmbientOrthogonality4D
end JanusFormal

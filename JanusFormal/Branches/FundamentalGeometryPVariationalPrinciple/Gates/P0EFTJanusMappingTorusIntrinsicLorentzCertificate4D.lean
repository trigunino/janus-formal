import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicLorentzCertificate4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private abbrev CoverTangent (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

private def spherePoint (point : UnitThreeSphere) : EuclideanR4 :=
  (unitThreeSphereHomeomorph point).1

private def sphereDiffeomorph :
    UnitThreeSphere ≃ₘ⟮(𝓡 3), (𝓡 3)⟯ StandardSphere where
  toEquiv := unitThreeSphereHomeomorph.toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph

private def coverDiffeomorphProd :
    EffectiveCover period hPeriod ≃ₘ⟮coverModelWithCorners,
      coverModelWithCorners⟯ (UnitThreeSphere × Real) where
  toEquiv := (coverHomeomorphProd (sphereData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd (sphereData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd (sphereData period hPeriod))

private abbrev SphereTangent (point : UnitThreeSphere) :=
  TangentSpace (𝓡 3) (unitThreeSphereHomeomorph point)

private abbrev SphereOrthogonal (point : UnitThreeSphere) :=
  (Real ∙ spherePoint point)ᗮ

private def standardSphereAmbientDerivative
    (point : UnitThreeSphere) : SphereTangent point →L[Real] EuclideanR4 :=
  mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
    ((↑) : StandardSphere → EuclideanR4)
    (unitThreeSphereHomeomorph point)

private def standardSphereDerivative
    (point : UnitThreeSphere) :
    SphereTangent point →L[Real] SphereOrthogonal point :=
  let derivative := standardSphereAmbientDerivative point
  derivative.codRestrict (SphereOrthogonal point) (fun vector => by
    change derivative vector ∈
      (Real ∙ ((unitThreeSphereHomeomorph point : StandardSphere) :
        EuclideanR4))ᗮ
    rw [← range_mfderiv_coe_sphere (n := 3)
      (unitThreeSphereHomeomorph point)]
    exact ⟨vector, rfl⟩)

private theorem standardSphereDerivative_bijective
    (point : UnitThreeSphere) :
    Function.Bijective (standardSphereDerivative point) := by
  constructor
  · intro first second h
    apply mfderiv_coe_sphere_injective (n := 3)
      (unitThreeSphereHomeomorph point)
    exact congrArg Subtype.val h
  · intro vector
    have hRange : (vector : EuclideanR4) ∈
        (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
          ((↑) : StandardSphere → EuclideanR4)
          (unitThreeSphereHomeomorph point)).range := by
      rw [range_mfderiv_coe_sphere (n := 3)
        (unitThreeSphereHomeomorph point)]
      change (vector : EuclideanR4) ∈ SphereOrthogonal point
      exact vector.2
    obtain ⟨preimage, hPreimage⟩ := hRange
    refine ⟨preimage, ?_⟩
    apply Subtype.ext
    exact hPreimage

private abbrev SphereCoordinates := EuclideanSpace Real (Fin 3)

private local instance sphereCoordinatesFiniteDimensional :
    FiniteDimensional Real SphereCoordinates := by
  change FiniteDimensional Real (EuclideanSpace Real (Fin 3))
  infer_instance

private def standardSphereDerivativeModel
    (point : UnitThreeSphere) :
    SphereCoordinates →L[Real] SphereOrthogonal point where
  toFun vector := standardSphereDerivative point vector
  map_add' first second := by
    exact (standardSphereDerivative point).map_add first second
  map_smul' scalar vector := by
    exact (standardSphereDerivative point).map_smul scalar vector
  cont := by
    exact (standardSphereDerivative point).continuous

private theorem standardSphereDerivativeModel_bijective
    (point : UnitThreeSphere) :
    Function.Bijective (standardSphereDerivativeModel point) := by
  constructor
  · intro first second h
    exact (standardSphereDerivative_bijective point).1 h
  · intro vector
    obtain ⟨preimage, hPreimage⟩ :=
      (standardSphereDerivative_bijective point).2 vector
    exact ⟨preimage, hPreimage⟩

private def standardSphereDerivativeEquiv
    (point : UnitThreeSphere) :
    SphereCoordinates ≃L[Real] SphereOrthogonal point :=
  (LinearEquiv.ofBijective (standardSphereDerivativeModel point).toLinearMap
    (standardSphereDerivativeModel_bijective point)).toContinuousLinearEquiv

@[simp]
private theorem standardSphereDerivativeEquiv_apply
    (point : UnitThreeSphere) (vector : SphereCoordinates) :
    ((standardSphereDerivativeEquiv point vector : SphereOrthogonal point) :
      EuclideanR4) =
      mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
        ((↑) : StandardSphere → EuclideanR4)
        (unitThreeSphereHomeomorph point) vector :=
  rfl

private def sphereDiffeomorphDerivativeEquiv
    (point : UnitThreeSphere) : SphereCoordinates ≃L[Real] SphereCoordinates :=
  (sphereDiffeomorph).mfderivToContinuousLinearEquiv (by simp) point

private def sphereToOrthogonalEquiv
    (point : UnitThreeSphere) :
    SphereCoordinates ≃L[Real] SphereOrthogonal point :=
  (sphereDiffeomorphDerivativeEquiv point).trans
    (standardSphereDerivativeEquiv point)

private theorem spherePoint_ne_zero (point : UnitThreeSphere) :
    spherePoint point ≠ 0 := by
  exact ne_zero_of_mem_unit_sphere (unitThreeSphereHomeomorph point)

private def sphereLorentzFrame
    (point : UnitThreeSphere) : SphereCoordinates ≃L[Real] SphereCoordinates :=
  (sphereToOrthogonalEquiv point).trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) 3
      (spherePoint_ne_zero point)).repr.toContinuousLinearEquiv

private def coverProductDerivativeEquiv
    (point : EffectiveCover period hPeriod) :
    CoverTangent period hPeriod point ≃L[Real] CoverCoordinates :=
  (coverDiffeomorphProd period hPeriod).mfderivToContinuousLinearEquiv
    (by simp) point

private def intrinsicCoverFrame
    (point : EffectiveCover period hPeriod) :
    CoverTangent period hPeriod point ≃L[Real] CoverCoordinates :=
  (coverProductDerivativeEquiv period hPeriod point).trans
    (ContinuousLinearEquiv.prodCongr (sphereLorentzFrame point.fiber)
      (ContinuousLinearEquiv.refl Real Real))

private theorem sphereAmbientDerivative_factor
    (point : UnitThreeSphere) :
    mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) spherePoint point =
      (standardSphereAmbientDerivative point).comp
        (sphereDiffeomorphDerivativeEquiv point :
          SphereCoordinates →L[Real] SphereCoordinates) := by
  have hInclusionSmooth : ContMDiff (𝓡 3) 𝓘(Real, EuclideanR4) ∞
      ((↑) : StandardSphere → EuclideanR4) :=
    contMDiff_coe_sphere
  have hInclusion : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point) :=
    hInclusionSmooth.mdifferentiableAt (by simp)
  have hSphere : MDifferentiableAt (𝓡 3) (𝓡 3)
      unitThreeSphereHomeomorph point :=
    sphereDiffeomorph.mdifferentiable (by simp) point
  change mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) spherePoint point =
    (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point)).comp
      (mfderiv (𝓡 3) (𝓡 3) unitThreeSphereHomeomorph point)
  have hMap : spherePoint =
      ((↑) : StandardSphere → EuclideanR4) ∘
        unitThreeSphereHomeomorph := by
    rfl
  rw [hMap]
  exact mfderiv_comp point hInclusion hSphere

private theorem sphereLorentzFrame_inner
    (point : UnitThreeSphere) (first second : SphereCoordinates) :
    inner Real
        (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) spherePoint point first)
        (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) spherePoint point second) =
      inner Real (sphereLorentzFrame point first)
        (sphereLorentzFrame point second) := by
  rw [sphereAmbientDerivative_factor]
  change inner Real
      ((sphereToOrthogonalEquiv point first : SphereOrthogonal point) :
        EuclideanR4)
      ((sphereToOrthogonalEquiv point second : SphereOrthogonal point) :
        EuclideanR4) =
    inner Real
      ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) 3
        (spherePoint_ne_zero point)).repr
          (sphereToOrthogonalEquiv point first))
      ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) 3
        (spherePoint_ne_zero point)).repr
          (sphereToOrthogonalEquiv point second))
  exact ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) 3
    (spherePoint_ne_zero point)).repr.inner_map_map
      (sphereToOrthogonalEquiv point first)
      (sphereToOrthogonalEquiv point second)).symm

private abbrev AmbientCoordinates := ModelProd EuclideanR4 Real

private abbrev ambientModelWithCorners :
    ModelWithCorners Real AmbientCoordinates AmbientCoordinates :=
  𝓘(Real, AmbientCoordinates)

private def productAmbientMap (point : UnitThreeSphere × Real) :
    AmbientCoordinates :=
  (spherePoint point.1, point.2)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem coverAmbientDerivative_factor
    (point : EffectiveCover period hPeriod) :
    coverAmbientDerivative period hPeriod point =
      ((mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) spherePoint point.fiber).prodMap
        (ContinuousLinearMap.id Real Real)).comp
        (coverProductDerivativeEquiv period hPeriod point :
          CoverTangent period hPeriod point →L[Real] CoverCoordinates) := by
  have hSphereSmooth : ContMDiff (𝓡 3) 𝓘(Real, EuclideanR4) ∞
      spherePoint := by
    have hInclusion : ContMDiff (𝓡 3) 𝓘(Real, EuclideanR4) ∞
        ((↑) : StandardSphere → EuclideanR4) :=
      contMDiff_coe_sphere
    exact hInclusion.comp sphereDiffeomorph.contMDiff
  have hSphere : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      spherePoint point.fiber :=
    hSphereSmooth.mdifferentiableAt (by simp)
  have hTime : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
      (id : Real → Real) point.time :=
    mdifferentiableAt_id
  have hProduct : MDifferentiableAt coverModelWithCorners
      ambientModelWithCorners productAmbientMap (point.fiber, point.time) := by
    have hProductMap : productAmbientMap = Prod.map spherePoint id := by
      rfl
    rw [hProductMap]
    change MDifferentiableAt coverModelWithCorners
      𝓘(Real, EuclideanR4 × Real) (Prod.map spherePoint id)
      (point.fiber, point.time)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hSphere.prodMap hTime
  have hCover : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners
      (coverHomeomorphProd (sphereData period hPeriod)) point :=
    (coverDiffeomorphProd period hPeriod).mdifferentiable (by simp) point
  have hMap : coverAmbientMap period hPeriod =
      productAmbientMap ∘
        (coverHomeomorphProd (sphereData period hPeriod)) := by
    funext current
    rfl
  have hProductDerivative :
      mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4 × Real)
          (Prod.map spherePoint id) (point.fiber, point.time) =
        (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) spherePoint
          point.fiber).prodMap (ContinuousLinearMap.id Real Real) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    rw [mfderiv_prodMap hSphere hTime, mfderiv_id]
    rfl
  rw [show coverAmbientDerivative period hPeriod point =
      mfderiv coverModelWithCorners ambientModelWithCorners
        (coverAmbientMap period hPeriod) point by rfl, hMap,
    mfderiv_comp point hProduct hCover,
    show productAmbientMap = Prod.map spherePoint id by rfl]
  change (mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4 × Real)
      (Prod.map spherePoint id) (point.fiber, point.time)).comp
      (mfderiv coverModelWithCorners coverModelWithCorners
        (coverHomeomorphProd (sphereData period hPeriod)) point) = _
  rw [hProductDerivative]
  rfl

private theorem coverAmbientDerivative_apply
    (point : EffectiveCover period hPeriod)
    (vector : CoverTangent period hPeriod point) :
    coverAmbientDerivative period hPeriod point vector =
      (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) spherePoint point.fiber
          (coverProductDerivativeEquiv period hPeriod point vector).1,
        (coverProductDerivativeEquiv period hPeriod point vector).2) := by
  rw [coverAmbientDerivative_factor]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem intrinsicCoverFrame_tensor_eq
    (point : EffectiveCover period hPeriod)
    (first second : CoverTangent period hPeriod point) :
    intrinsicCoverLorentzTensor period hPeriod point first second =
      modelMinkowskiPair
        (intrinsicCoverFrame period hPeriod point first)
        (intrinsicCoverFrame period hPeriod point second) := by
  rw [intrinsicCoverLorentzTensor_apply]
  unfold modelMinkowskiPair
  rw [coverAmbientDerivative_apply, coverAmbientDerivative_apply,
    sphereLorentzFrame_inner]
  rfl

def intrinsicCoverLorentzCertificate :
    IntrinsicCoverLorentzCertificate period hPeriod where
  frame := intrinsicCoverFrame period hPeriod
  tensor_eq_model := intrinsicCoverFrame_tensor_eq period hPeriod

theorem intrinsicQuotientTensor_isEverywhereLorentzian :
    IsEverywhereLorentzian period hPeriod
      (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor :=
  (intrinsicCoverLorentzCertificate period hPeriod).quotient_lorentzian

end
end P0EFTJanusMappingTorusIntrinsicLorentzCertificate4D
end JanusFormal

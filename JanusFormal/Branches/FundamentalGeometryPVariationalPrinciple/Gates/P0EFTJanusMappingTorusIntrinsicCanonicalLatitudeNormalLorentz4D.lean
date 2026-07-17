import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D

/-!
# Lorentz geometry of the canonical latitude normal

This gate computes the intrinsic Lorentz square of the explicit latitude
normal and proves its orthogonality to the differential of the fixed-throat
inclusion on the genuine mapping-torus cover.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

private abbrev ThroatTangent (anchor : EffectiveThroatCover period hPeriod) :=
  TangentSpace throatCoverModelWithCorners anchor

/-- Ambient covector extracting the reflected spatial coordinate. -/
def ambientLatitudeCoordinate : (EuclideanR4 × Real) →L[Real] Real :=
  (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 4)).comp
    (ContinuousLinearMap.fst Real EuclideanR4 Real)

@[simp]
theorem ambientLatitudeCoordinate_apply (point : EuclideanR4 × Real) :
    ambientLatitudeCoordinate point = point.1 (0 : Fin 4) := by
  rfl

/-- The reflected ambient coordinate vanishes identically on the actual
equatorial inclusion. -/
theorem sphereAmbientMap_equatorialSphereInclusion_latitudeCoordinate
    (point : EquatorialTwoSphere) :
    (sphereAmbientMap (equatorialSphereInclusion point)) (0 : Fin 4) = 0 := by
  have hConjugacy := congrArg (fun sphere => unitThreeSphereHomeomorph sphere)
    (standardEquatorInclusion_conjugates_actual point)
  simp only [Homeomorph.apply_symm_apply] at hConjugacy
  change (unitThreeSphereHomeomorph
    (equatorialSphereInclusion point)).1 (0 : Fin 4) = 0
  rw [← hConjugacy]
  simp only [standardEquatorInclusion, euclideanEquatorInsert]
  rfl

/-- Reflected coordinate of the genuine sphere ambient map. -/
def sphereLatitudeCoordinate (point : UnitThreeSphere) : Real :=
  EuclideanSpace.proj (𝕜 := Real) (0 : Fin 4) (sphereAmbientMap point)

theorem sphereLatitudeCoordinate_contMDiff :
    ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ sphereLatitudeCoordinate := by
  exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 4)).contDiff.contMDiff.comp
    sphereAmbientMap_contMDiff

@[simp]
theorem sphereLatitudeCoordinate_equatorialSphereInclusion
    (point : EquatorialTwoSphere) :
    sphereLatitudeCoordinate (equatorialSphereInclusion point) = 0 :=
  sphereAmbientMap_equatorialSphereInclusion_latitudeCoordinate point

/-- The ambient derivative of every actual equatorial-sphere tangent has
zero reflected coordinate. -/
theorem sphereAmbientDerivative_equatorialTangent_latitudeCoordinate_zero
    (point : EquatorialTwoSphere)
    (tangent : TangentSpace (𝓡 2) point) :
    (show EuclideanR4 from
      mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
        (equatorialSphereInclusion point)
        (mfderiv (𝓡 2) (𝓡 3) equatorialSphereInclusion point tangent))
      (0 : Fin 4) = 0 := by
  have hAmbient : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      sphereAmbientMap (equatorialSphereInclusion point) :=
    sphereAmbientMap_contMDiff.mdifferentiableAt (by simp)
  have hCoordinate : MDifferentiableAt 𝓘(Real, EuclideanR4) 𝓘(Real, Real)
      (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 4))
      (sphereAmbientMap (equatorialSphereInclusion point)) :=
    (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 4)).differentiableAt.mdifferentiableAt
  let equatorTangent :=
    mfderiv (𝓡 2) (𝓡 3) equatorialSphereInclusion point tangent
  have hCoordinateDerivative :
      mfderiv (𝓡 3) 𝓘(Real, Real) sphereLatitudeCoordinate
          (equatorialSphereInclusion point) equatorTangent =
        (show EuclideanR4 from
          mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
            (equatorialSphereInclusion point) equatorTangent) (0 : Fin 4) := by
    have hChain :=
      mfderiv_comp_apply (equatorialSphereInclusion point)
        hCoordinate hAmbient equatorTangent
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
    convert hChain using 1 <;> rfl
  have hInclusion : MDifferentiableAt (𝓡 2) (𝓡 3)
      equatorialSphereInclusion point :=
    equatorialSphereInclusion_contMDiff.mdifferentiableAt (by simp)
  have hLatitude : MDifferentiableAt (𝓡 3) 𝓘(Real, Real)
      sphereLatitudeCoordinate (equatorialSphereInclusion point) :=
    sphereLatitudeCoordinate_contMDiff.mdifferentiableAt (by simp)
  have hAlongEquator :=
    mfderiv_comp_apply point hLatitude hInclusion tangent
  have hConstant :
      sphereLatitudeCoordinate ∘ equatorialSphereInclusion =
        fun _ : EquatorialTwoSphere => 0 := by
    funext source
    exact sphereLatitudeCoordinate_equatorialSphereInclusion source
  rw [hConstant, mfderiv_const] at hAlongEquator
  change (0 : Real) = mfderiv (𝓡 3) 𝓘(Real, Real)
    sphereLatitudeCoordinate (equatorialSphereInclusion point)
      equatorTangent at hAlongEquator
  exact hCoordinateDerivative.symm.trans hAlongEquator.symm

/-- Product-coordinate naturality of the actual fixed-throat differential. -/
theorem coverProductDerivative_fixedThroatCoverInclusion
    (anchor : EffectiveThroatCover period hPeriod)
    (tangent : ThroatTangent period hPeriod anchor) :
    coverProductDerivative period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) anchor tangent) =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
          (Prod.map equatorialSphereInclusion (id : Real → Real))
          (anchor.fiber, anchor.time)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (coverHomeomorphProd (throatData period hPeriod)) anchor tangent) := by
  let sourceHomeomorph := coverHomeomorphProd (throatData period hPeriod)
  let targetHomeomorph := coverHomeomorphProd (sphereData period hPeriod)
  let productInclusion :=
    Prod.map equatorialSphereInclusion (id : Real → Real)
  have hSource : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners sourceHomeomorph anchor :=
    (chartedSpacePullback_toFun_contMDiff throatCoverModelWithCorners ∞
      sourceHomeomorph).mdifferentiableAt (by simp)
  have hTarget : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners targetHomeomorph
      (fixedThroatCoverInclusion period hPeriod anchor) :=
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      targetHomeomorph).mdifferentiableAt (by simp)
  have hInclusion : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatCoverInclusion period hPeriod) anchor :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hProduct : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners productInclusion (sourceHomeomorph anchor) :=
    (equatorialSphereInclusion_contMDiff.prodMap contMDiff_id)
      |>.mdifferentiableAt (by simp)
  have hDerivative :
      (mfderiv coverModelWithCorners coverModelWithCorners targetHomeomorph
          (fixedThroatCoverInclusion period hPeriod anchor)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) anchor) =
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
          productInclusion (sourceHomeomorph anchor)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          sourceHomeomorph anchor) := by
    rw [← mfderiv_comp anchor hTarget hInclusion,
      ← mfderiv_comp anchor hProduct hSource]
    rfl
  exact congrArg (fun derivative => derivative tangent) hDerivative

/-- Every tangent carried by the fixed-throat inclusion has zero reflected
coordinate in the genuine ambient derivative. -/
theorem coverAmbientDerivative_fixedThroat_latitudeCoordinate_zero
    (anchor : EffectiveThroatCover period hPeriod)
    (tangent : ThroatTangent period hPeriod anchor) :
    (coverAmbientDerivative period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) anchor tangent)).1
      (0 : Fin 4) = 0 := by
  let sourceTangent :=
    mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
      (coverHomeomorphProd (throatData period hPeriod)) anchor tangent
  have hProduct := coverProductDerivative_fixedThroatCoverInclusion
    period hPeriod anchor tangent
  have hSphere : MDifferentiableAt (𝓡 2) (𝓡 3)
      equatorialSphereInclusion anchor.fiber :=
    equatorialSphereInclusion_contMDiff.mdifferentiableAt (by simp)
  have hTime : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
      (id : Real → Real) anchor.time :=
    mdifferentiableAt_id
  rw [mfderiv_prodMap hSphere hTime] at hProduct
  have hSpatial := congrArg Prod.fst hProduct
  change
    (coverProductDerivative period hPeriod
      (fixedThroatCoverInclusion period hPeriod anchor)
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod) anchor tangent)).1 =
      mfderiv (𝓡 2) (𝓡 3) equatorialSphereInclusion anchor.fiber
        sourceTangent.1 at hSpatial
  rw [coverAmbientDerivative_apply_product, hSpatial]
  exact sphereAmbientDerivative_equatorialTangent_latitudeCoordinate_zero
    anchor.fiber sourceTangent.1

/-- With the ambient convention `spatial - time`, the canonical latitude
normal has positive unit Lorentz square. -/
theorem intrinsicCoverLorentzTensor_latitudeNormal_square
    (anchor : EffectiveThroatCover period hPeriod) :
    intrinsicCoverLorentzTensor period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) = 1 := by
  rw [intrinsicCoverLorentzTensor_apply,
    coverAmbientDerivative_latitudeNormal]
  simp

/-- The canonical latitude normal is orthogonal, for the actual intrinsic
Lorentz tensor, to every tangent in the genuine fixed-throat differential. -/
theorem intrinsicCoverLorentzTensor_latitudeNormal_orthogonal
    (anchor : EffectiveThroatCover period hPeriod)
    (tangent : ThroatTangent period hPeriod anchor) :
    intrinsicCoverLorentzTensor period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) anchor tangent) = 0 := by
  rw [intrinsicCoverLorentzTensor_apply,
    coverAmbientDerivative_latitudeNormal]
  have hZero := coverAmbientDerivative_fixedThroat_latitudeCoordinate_zero
    period hPeriod anchor tangent
  simpa [EuclideanSpace.inner_single_left] using hZero

/-- Hence the canonical cover normal is spacelike in the convention
`spatial - time`. -/
theorem intrinsicCoverLorentzTensor_latitudeNormal_spacelike
    (anchor : EffectiveThroatCover period hPeriod) :
    0 < intrinsicCoverLorentzTensor period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) := by
  rw [intrinsicCoverLorentzTensor_latitudeNormal_square]
  exact zero_lt_one

/-- In particular, the canonical cover normal is non-null. -/
theorem intrinsicCoverLorentzTensor_latitudeNormal_nonnull
    (anchor : EffectiveThroatCover period hPeriod) :
    intrinsicCoverLorentzTensor period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) ≠ 0 := by
  rw [intrinsicCoverLorentzTensor_latitudeNormal_square]
  exact one_ne_zero

end

end P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D
end JanusFormal

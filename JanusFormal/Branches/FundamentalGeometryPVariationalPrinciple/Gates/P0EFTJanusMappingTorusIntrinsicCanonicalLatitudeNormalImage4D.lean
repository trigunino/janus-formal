import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D

/-!
# Intrinsic ambient image of the canonical latitude normal

This gate identifies the product-coordinate derivative of the cover with the
derivative equivalence of its global product diffeomorphism.  It then computes
the canonical latitude normal in product and ambient coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D

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

private abbrev CoverTangent (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- The global product homeomorphism of the cover, upgraded to a smooth
diffeomorphism. -/
def coverProductDiffeomorph :
    EffectiveCover period hPeriod ≃ₘ⟮coverModelWithCorners,
      coverModelWithCorners⟯ (UnitThreeSphere × Real) where
  toEquiv := (coverHomeomorphProd (sphereData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd (sphereData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd (sphereData period hPeriod))

/-- The public product derivative is an equivalence on every cover tangent
fiber. -/
def coverProductDerivativeEquiv
    (point : EffectiveCover period hPeriod) :
    CoverTangent period hPeriod point ≃L[Real] CoverCoordinates :=
  (coverProductDiffeomorph period hPeriod).mfderivToContinuousLinearEquiv
    (by simp) point

@[simp]
theorem coverProductDerivativeEquiv_toContinuousLinearMap
    (point : EffectiveCover period hPeriod) :
    (coverProductDerivativeEquiv period hPeriod point :
      CoverTangent period hPeriod point →L[Real] CoverCoordinates) =
      coverProductDerivative period hPeriod point := by
  rfl

/-- In product coordinates, the latitude normal has the derivative of the
sphere latitude in its first component and zero time component. -/
theorem coverProductDerivative_latitudeNormalAtZero
    (anchor : EffectiveThroatCover period hPeriod) :
    coverProductDerivative period hPeriod
        (normalLatitudeCover period hPeriod anchor 0)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) 0 1) =
      (mfderiv 𝓘(Real, Real) (𝓡 3)
          (equatorialLatitude anchor.fiber) 0 1, 0) := by
  have hOuter : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (coverHomeomorphProd (sphereData period hPeriod))
      (normalLatitudeCover period hPeriod anchor 0) :=
    (coverProductDiffeomorph period hPeriod).mdifferentiable (by simp) _
  have hInner : MDifferentiableAt 𝓘(Real, Real) coverModelWithCorners
      (normalLatitudeCover period hPeriod anchor) 0 :=
    (normalLatitudeCover_contMDiff period hPeriod anchor).mdifferentiableAt
      (by simp)
  have hComposition := mfderiv_comp_apply 0 hOuter hInner 1
  have hSphere : MDifferentiableAt 𝓘(Real, Real) (𝓡 3)
      (equatorialLatitude anchor.fiber) 0 :=
    (equatorialLatitude_contMDiff anchor.fiber).mdifferentiableAt (by simp)
  have hProductDerivative :
      mfderiv 𝓘(Real, Real) coverModelWithCorners
          (fun normal => (equatorialLatitude anchor.fiber normal, anchor.time)) 0 1 =
        (mfderiv 𝓘(Real, Real) (𝓡 3)
          (equatorialLatitude anchor.fiber) 0 1, 0) := by
    rw [mfderiv_prodMk hSphere mdifferentiableAt_const]
    rw [mfderiv_const]
    rfl
  rw [← hProductDerivative]
  exact hComposition.symm

/-- The preceding formula at the actual throat point and its named canonical
normal vector. -/
theorem coverProductDerivative_latitudeNormal
    (anchor : EffectiveThroatCover period hPeriod) :
    coverProductDerivative period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) =
      (mfderiv 𝓘(Real, Real) (𝓡 3)
          (equatorialLatitude anchor.fiber) 0 1, 0) := by
  rw [← normalLatitudeCover_zero period hPeriod anchor]
  exact coverProductDerivative_latitudeNormalAtZero period hPeriod anchor

/-- The ambient computation before transporting the zero-latitude point to
the named throat inclusion. -/
theorem coverAmbientDerivative_latitudeNormalAtZero
    (anchor : EffectiveThroatCover period hPeriod) :
    coverAmbientDerivative period hPeriod
        (normalLatitudeCover period hPeriod anchor 0)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) 0 1) =
      (EuclideanSpace.single (0 : Fin 4) 1, 0) := by
  rw [coverAmbientDerivative_apply_product,
    coverProductDerivative_latitudeNormalAtZero]
  change
    (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
        (equatorialLatitude anchor.fiber 0)
        (mfderiv 𝓘(Real, Real) (𝓡 3)
          (equatorialLatitude anchor.fiber) 0 1), 0) = _
  have hSphere : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      sphereAmbientMap (equatorialLatitude anchor.fiber 0) :=
    sphereAmbientMap_contMDiff.mdifferentiableAt (by simp)
  have hLatitude : MDifferentiableAt 𝓘(Real, Real) (𝓡 3)
      (equatorialLatitude anchor.fiber) 0 :=
    (equatorialLatitude_contMDiff anchor.fiber).mdifferentiableAt (by simp)
  have hComposition := mfderiv_comp_apply 0 hSphere hLatitude 1
  have hMap : sphereAmbientMap ∘ equatorialLatitude anchor.fiber =
      fun normal =>
        (unitThreeSphereHomeomorph
          (equatorialLatitude anchor.fiber normal)).1 := by
    rfl
  have hFirstFDeriv :=
    (latitudeAmbient_hasFDerivAt anchor.fiber anchor.time).fst
  have hFirst :
      mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR4)
          (fun normal =>
            (unitThreeSphereHomeomorph
              (equatorialLatitude anchor.fiber normal)).1) 0 1 =
        EuclideanSpace.single (0 : Fin 4) 1 := by
    rw [mfderiv_eq_fderiv, hFirstFDeriv.fderiv]
    change (latitudeAmbientDerivative 1).1 = _
    rw [latitudeAmbientDerivative_one]
  rw [hMap, hFirst] at hComposition
  exact Prod.ext hComposition.symm rfl

/-- The ambient image of the canonical latitude normal is the first Euclidean
basis vector and has no time component. -/
theorem coverAmbientDerivative_latitudeNormal
    (anchor : EffectiveThroatCover period hPeriod) :
    coverAmbientDerivative period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) =
      (EuclideanSpace.single (0 : Fin 4) 1, 0) := by
  rw [← normalLatitudeCover_zero period hPeriod anchor]
  exact coverAmbientDerivative_latitudeNormalAtZero period hPeriod anchor

theorem coverAmbientDerivative_latitudeNormal_ne_zero
    (anchor : EffectiveThroatCover period hPeriod) :
    coverAmbientDerivative period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) ≠ 0 := by
  rw [coverAmbientDerivative_latitudeNormal]
  intro hZero
  have hFirst : EuclideanSpace.single (0 : Fin 4) (1 : Real) = 0 :=
    congrArg Prod.fst hZero
  exact one_ne_zero (EuclideanSpace.single_eq_zero_iff.mp hFirst)

theorem coverLatitudeNormalVector_ne_zero
    (anchor : EffectiveThroatCover period hPeriod) :
    coverLatitudeNormalVector period hPeriod anchor ≠ 0 := by
  intro hZero
  apply coverAmbientDerivative_latitudeNormal_ne_zero period hPeriod anchor
  rw [hZero, map_zero]

end

end P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D
end JanusFormal

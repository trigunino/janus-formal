import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-!
# Scalar Green current on the genuine canonical latitude normal

The collar Wronskian is promoted to a tangent vector along the actual
quotient latitude curve.  The intrinsic D8 metric makes that normal unit, so
the metric normal flux of the tangent current is exactly the scalar
Wronskian.  Conservation below is only differentiation in the explicit
latitude coordinate; no global four-dimensional divergence or Stokes theorem
is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

/-- Ambient Euclidean velocity of the latitude curve at an arbitrary normal
coordinate. -/
def latitudeAmbientVelocity
    (point : EquatorialTwoSphere) (normal : Real) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm
    (Fin.cases (Real.cos normal)
      (fun index : Fin 3 => -Real.sin normal * point.1 index.succ))

private def latitudeAmbientVelocityDerivative
    (point : EquatorialTwoSphere) (normal : Real) :
    Real →L[Real] EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun index : Fin 4 =>
      Fin.cases (ContinuousLinearMap.toSpanSingleton Real (Real.cos normal))
        (fun tail : Fin 3 =>
          ContinuousLinearMap.toSpanSingleton Real
            (-Real.sin normal * point.1 tail.succ)) index)

private theorem latitudeAmbient_hasFDerivAt
    (point : EquatorialTwoSphere) (normal : Real) :
    HasFDerivAt
      (fun coordinate : Real =>
        (unitThreeSphereHomeomorph
          (equatorialLatitude point coordinate)).1)
      (latitudeAmbientVelocityDerivative point normal) normal := by
  have hCoordinates : HasFDerivAt
      (fun coordinate : Real => fun index : Fin 4 =>
        Fin.cases (motive := fun _ => Real) (Real.sin coordinate)
          (fun tail : Fin 3 => Real.cos coordinate * point.1 tail.succ) index)
      (ContinuousLinearMap.pi fun index : Fin 4 =>
        Fin.cases (motive := fun _ => Real →L[Real] Real)
          (ContinuousLinearMap.toSpanSingleton Real (Real.cos normal))
          (fun tail : Fin 3 =>
            ContinuousLinearMap.toSpanSingleton Real
              (-Real.sin normal * point.1 tail.succ)) index)
      normal := by
    rw [hasFDerivAt_pi]
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · simpa using (Real.hasDerivAt_sin normal).hasFDerivAt
    · simpa [mul_comm] using
        ((Real.hasDerivAt_cos normal).mul_const
          (point.1 tail.succ)).hasFDerivAt
  exact
    (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.hasFDerivAt.comp
      normal hCoordinates

@[simp]
theorem latitudeAmbientVelocityDerivative_one
    (point : EquatorialTwoSphere) (normal : Real) :
    latitudeAmbientVelocityDerivative point normal 1 =
      latitudeAmbientVelocity point normal := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index <;>
    simp [latitudeAmbientVelocityDerivative, latitudeAmbientVelocity]

/-- In the global product coordinates, the cover latitude tangent is the
sphere latitude tangent with zero time component. -/
theorem coverProductDerivative_normalLatitude
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    coverProductDerivative period hPeriod
        (normalLatitudeCover period hPeriod anchor normal)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) normal 1) =
      (mfderiv 𝓘(Real, Real) (𝓡 3)
          (equatorialLatitude anchor.fiber) normal 1, 0) := by
  have hOuter : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (coverHomeomorphProd (sphereData period hPeriod))
      (normalLatitudeCover period hPeriod anchor normal) :=
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (sphereData period hPeriod))).mdifferentiableAt
        (by simp)
  have hInner : MDifferentiableAt 𝓘(Real, Real) coverModelWithCorners
      (normalLatitudeCover period hPeriod anchor) normal :=
    (normalLatitudeCover_contMDiff period hPeriod anchor).mdifferentiableAt
      (by simp)
  have hComposition := mfderiv_comp_apply normal hOuter hInner 1
  change
    mfderiv coverModelWithCorners coverModelWithCorners
        (coverHomeomorphProd (sphereData period hPeriod))
        (normalLatitudeCover period hPeriod anchor normal)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) normal 1) = _
  have hSphere : MDifferentiableAt 𝓘(Real, Real) (𝓡 3)
      (equatorialLatitude anchor.fiber) normal :=
    (equatorialLatitude_contMDiff anchor.fiber).mdifferentiableAt (by simp)
  have hProductDerivative :
      mfderiv 𝓘(Real, Real) coverModelWithCorners
          (fun coordinate =>
            (equatorialLatitude anchor.fiber coordinate, anchor.time))
          normal 1 =
        (mfderiv 𝓘(Real, Real) (𝓡 3)
          (equatorialLatitude anchor.fiber) normal 1, 0) := by
    rw [mfderiv_prodMk hSphere mdifferentiableAt_const, mfderiv_const]
    rfl
  rw [← hProductDerivative]
  exact hComposition.symm

/-- The true cover-immersion derivative sends the cover latitude tangent to
the explicit Euclidean latitude velocity and zero time velocity. -/
theorem coverAmbientDerivative_normalLatitude
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    coverAmbientDerivative period hPeriod
        (normalLatitudeCover period hPeriod anchor normal)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) normal 1) =
      (latitudeAmbientVelocity anchor.fiber normal, 0) := by
  rw [coverAmbientDerivative_apply_product,
    coverProductDerivative_normalLatitude]
  change
    (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
        (equatorialLatitude anchor.fiber normal)
        (mfderiv 𝓘(Real, Real) (𝓡 3)
          (equatorialLatitude anchor.fiber) normal 1), 0) = _
  have hSphere : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      sphereAmbientMap (equatorialLatitude anchor.fiber normal) :=
    sphereAmbientMap_contMDiff.mdifferentiableAt (by simp)
  have hLatitude : MDifferentiableAt 𝓘(Real, Real) (𝓡 3)
      (equatorialLatitude anchor.fiber) normal :=
    (equatorialLatitude_contMDiff anchor.fiber).mdifferentiableAt (by simp)
  have hComposition := mfderiv_comp_apply normal hSphere hLatitude 1
  have hCurveDerivative :
      mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR4)
          (fun coordinate : Real =>
            (unitThreeSphereHomeomorph
              (equatorialLatitude anchor.fiber coordinate)).1)
          normal 1 = latitudeAmbientVelocity anchor.fiber normal := by
    rw [mfderiv_eq_fderiv,
      (latitudeAmbient_hasFDerivAt anchor.fiber normal).fderiv]
    convert latitudeAmbientVelocityDerivative_one anchor.fiber normal using 1 <;>
      rfl
  rw [← hCurveDerivative]
  exact Prod.ext hComposition.symm rfl

/-- The ambient latitude velocity has Euclidean squared length one. -/
theorem latitudeAmbientVelocity_inner_self
    (point : EquatorialTwoSphere) (normal : Real) :
    inner Real (latitudeAmbientVelocity point normal)
      (latitudeAmbientVelocity point normal) = 1 := by
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  unfold latitudeAmbientVelocity
  rw [Fin.sum_univ_four]
  have hEquator := point.2.1
  unfold OnUnitThreeSphere radiusSquared at hEquator
  rw [Fin.sum_univ_succ, point.2.2] at hEquator
  rw [Fin.sum_univ_three] at hEquator
  norm_num at hEquator
  change point.1 1 ^ 2 + point.1 2 ^ 2 + point.1 3 ^ 2 = 1 at hEquator
  change
    Real.cos normal ^ 2 +
        (-Real.sin normal * point.1 1) ^ 2 +
        (-Real.sin normal * point.1 2) ^ 2 +
        (-Real.sin normal * point.1 3) ^ 2 = 1
  nlinarith [Real.sin_sq_add_cos_sq normal]

/-- The intrinsic cover metric makes every latitude tangent unit spacelike. -/
theorem intrinsicCoverLorentzTensor_normalLatitude_self
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    intrinsicCoverLorentzTensor period hPeriod
        (normalLatitudeCover period hPeriod anchor normal)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) normal 1)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) normal 1) = 1 := by
  rw [intrinsicCoverLorentzTensor_apply,
    coverAmbientDerivative_normalLatitude,
    latitudeAmbientVelocity_inner_self]
  norm_num

/-- The quotient latitude tangent is the quotient-projection derivative of
the cover latitude tangent. -/
theorem canonicalLatitudeNormalVector_eq_projectionDerivative
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeNormalVector period hPeriod base normal =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (normalLatitudeCover period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod
            (canonicalLatitudeAnchor period hPeriod base)) normal 1) := by
  have hOuter : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod))
      (normalLatitudeCover period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hInner : MDifferentiableAt 𝓘(Real, Real) coverModelWithCorners
      (normalLatitudeCover period hPeriod
        (canonicalLatitudeAnchor period hPeriod base)) normal :=
    (normalLatitudeCover_contMDiff period hPeriod
      (canonicalLatitudeAnchor period hPeriod base)).mdifferentiableAt (by simp)
  exact mfderiv_comp_apply normal hOuter hInner 1

/-- The actual quotient collar normal is unit for the intrinsic D8 metric. -/
theorem intrinsicMetric_canonicalLatitudeNormalVector_self
    (base : CanonicalLatitudeBase) (normal : Real) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal)
        (canonicalLatitudeNormalVector period hPeriod base normal)
        (canonicalLatitudeNormalVector period hPeriod base normal) = 1 := by
  let anchor := canonicalLatitudeAnchor period hPeriod base
  let point := normalLatitudeCover period hPeriod anchor normal
  let vector := mfderiv 𝓘(Real, Real) coverModelWithCorners
    (normalLatitudeCover period hPeriod anchor) normal 1
  change (intrinsicTensorQuotientDescent period hPeriod).tensor
      (mappingTorusMk (sphereData period hPeriod) point)
      (canonicalLatitudeNormalVector period hPeriod base normal)
      (canonicalLatitudeNormalVector period hPeriod base normal) = 1
  rw [canonicalLatitudeNormalVector_eq_projectionDerivative]
  exact ((intrinsicTensorQuotientDescent period hPeriod).pullback
    point vector vector).trans
      (intrinsicCoverLorentzTensor_normalLatitude_self period hPeriod
        anchor normal)

/-- Genuine tangent current along the quotient collar.  This is a section
only along the explicit latitude curve, not a global spacetime vector field. -/
def canonicalLatitudeScalarNormalCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    TangentSpace coverModelWithCorners
      (quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal) :=
  canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal •
    canonicalLatitudeNormalVector period hPeriod base normal

/-- Metric flux of the tangent current across its canonical unit normal. -/
def canonicalLatitudeScalarNormalFlux
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
    (quotientNormalLatitude period hPeriod
      (canonicalLatitudeAnchor period hPeriod base) normal)
    (canonicalLatitudeScalarNormalCurrent period hPeriod field test base normal)
    (canonicalLatitudeNormalVector period hPeriod base normal)

/-- The normal flux of the genuine tangent current is exactly the scalar
Green--Wronskian current. -/
theorem canonicalLatitudeScalarNormalFlux_eq_greenCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarNormalFlux period hPeriod field test base normal =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal := by
  unfold canonicalLatitudeScalarNormalFlux canonicalLatitudeScalarNormalCurrent
  rw [map_smul]
  simp only [smul_apply, smul_eq_mul]
  rw [intrinsicMetric_canonicalLatitudeNormalVector_self, mul_one]

/-- Local divergence-along-latitude vanishes for two equal-mass collar Euler
solutions. -/
theorem canonicalLatitudeScalarNormalFlux_hasDerivAt_zero_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real) :
    CanonicalLatitudeScalarHasDerivAt
      (canonicalLatitudeScalarNormalFlux period hPeriod field test base)
      0 normal := by
  rw [show canonicalLatitudeScalarNormalFlux period hPeriod field test base =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base from
    funext fun coordinate =>
      canonicalLatitudeScalarNormalFlux_eq_greenCurrent period hPeriod
        field test base coordinate]
  exact canonicalLatitudeScalarGreenCurrent_hasDerivAt_zero_of_euler period
    hPeriod massSquared field test hField hTest base normal

/-- The genuine normal flux is constant between any two coordinates on one
canonical latitude fiber for equal-mass Euler solutions. -/
theorem canonicalLatitudeScalarNormalFlux_eq_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (first second : Real) :
    canonicalLatitudeScalarNormalFlux period hPeriod field test base first =
      canonicalLatitudeScalarNormalFlux period hPeriod field test base second := by
  rw [canonicalLatitudeScalarNormalFlux_eq_greenCurrent,
    canonicalLatitudeScalarNormalFlux_eq_greenCurrent]
  exact canonicalLatitudeScalarGreenCurrent_eq_of_euler period hPeriod
    massSquared field test hField hTest base first second

/-- The endpoint jump of the genuine normal flux is the antisymmetrization
of the concrete collar boundary functional. -/
theorem canonicalLatitudeScalarNormalFlux_endpointJump_eq_boundary_antisymm
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarNormalFlux period hPeriod field test base 1 -
        canonicalLatitudeScalarNormalFlux period hPeriod field test base 0 =
      canonicalLatitudeScalarBoundaryFiber period hPeriod test field base -
        canonicalLatitudeScalarBoundaryFiber period hPeriod field test base := by
  rw [canonicalLatitudeScalarNormalFlux_eq_greenCurrent,
    canonicalLatitudeScalarNormalFlux_eq_greenCurrent]
  exact
    canonicalLatitudeScalarGreenCurrent_endpointJump_eq_boundary_antisymm
      period hPeriod field test base

/-- At the physical throat, the flux uses the actual manifold directional
differentials along the canonical quotient normal. -/
theorem canonicalLatitudeScalarNormalFlux_zero_eq_mvfderiv_pairing
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarNormalFlux period hPeriod field test base 0 =
      canonicalLatitudeValue period hPeriod field base 0 *
          mvfderiv coverModelWithCorners test.toFun
            (quotientNormalLatitude period hPeriod
              (canonicalLatitudeAnchor period hPeriod base) 0)
            (canonicalLatitudeNormalVector period hPeriod base 0) -
        canonicalLatitudeValue period hPeriod test base 0 *
          mvfderiv coverModelWithCorners field.toFun
            (quotientNormalLatitude period hPeriod
              (canonicalLatitudeAnchor period hPeriod base) 0)
            (canonicalLatitudeNormalVector period hPeriod base 0) := by
  rw [canonicalLatitudeScalarNormalFlux_eq_greenCurrent,
    canonicalLatitudeScalarGreenCurrent_eq_normalNoetherPairing,
    canonicalLatitudeDerivative_eq_mvfderiv_normal,
    canonicalLatitudeDerivative_eq_mvfderiv_normal]

end

end P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
end JanusFormal

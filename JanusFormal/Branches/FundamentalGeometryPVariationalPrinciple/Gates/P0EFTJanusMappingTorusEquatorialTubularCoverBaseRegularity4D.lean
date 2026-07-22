import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D

/-!
# Smooth normalized-tail inverse on the equatorial tubular band

The only remaining coordinate regularity input for the explicit tubular inverse
was smoothness of the normalized equatorial tail

`x ↦ tail(x) / cos (arcsin x₀)`

as an `S²`-valued map on the open band `|x₀| < 1`.

This file proves that statement directly.  Every ambient coordinate of the
sphere fiber is smooth on the reflected-sphere cover, `arcsin` is smooth on the
open band, and the cosine denominator is strictly positive there.  The
normalized tail is therefore a smooth `R³`-valued map.  Its already-proved unit
norm lets us codomain-restrict it to the standard two-sphere.

A harmless fallback value extends this map to the whole cover.  Since the band
is open, the extension is smooth at every band point and agrees there with the
explicit algebraic inverse.  Consequently the complete physical tubular inverse
regularity package is now a theorem rather than an external input.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusEquatorialTubularCoverBaseRegularity4D

set_option autoImplicit false
noncomputable section

open Set Metric Topology Filter
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1
private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- Every ambient coordinate of the transported algebraic unit three-sphere is
smooth. -/
theorem canonicalLatitudeSphereCoordinate_contMDiff
    (index : Fin 4) :
    ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
      (fun point : UnitThreeSphere => point.1 index) := by
  letI : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  have hAmbient : ContMDiff (𝓡 3) 𝓘(Real, R4Point) ∞
      (fun point : StandardSphere3 =>
        EuclideanSpace.equiv (Fin 4) Real point.1) := by
    exact (EuclideanSpace.equiv (Fin 4) Real).contDiff.contMDiff.comp
      contMDiff_coe_sphere
  have hCoordinate : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
      (fun point : StandardSphere3 =>
        (EuclideanSpace.equiv (Fin 4) Real point.1) index) :=
    (contDiff_apply Real Real index).contMDiff.comp hAmbient
  exact (hCoordinate.comp hTo).congr fun point => rfl

/-- Every sphere-fiber coordinate is smooth on the reflected mapping-torus
cover. -/
theorem canonicalLatitudeCoverSphereCoordinate_contMDiff
    (index : Fin 4) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : EffectiveCover period hPeriod => point.fiber.1 index) := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞
    (coverHomeomorphProd (sphereData period hPeriod))
  have hProduct : ContMDiff
      ((𝓡 3).prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun point : UnitThreeSphere × Real => point.1.1 index) :=
    (canonicalLatitudeSphereCoordinate_contMDiff index).comp contMDiff_fst
  exact (hProduct.comp hTo).congr fun point => rfl

/-- The open tubular band as an `Opens`, so that its subtype inherits the cover
manifold structure. -/
def canonicalLatitudeCoverTubularBandOpen :
    TopologicalSpace.Opens (EffectiveCover period hPeriod) :=
  ⟨canonicalLatitudeCoverTubularBand period hPeriod,
    canonicalLatitudeCoverTubularBand_isOpen period hPeriod⟩

private abbrev BandCover :=
  canonicalLatitudeCoverTubularBandOpen period hPeriod

/-- Signed normal restricted to the open band. -/
def canonicalLatitudeBandSignedNormal
    (point : BandCover period hPeriod) : Real :=
  canonicalLatitudeCoverSignedNormal period hPeriod point.1

/-- Smoothness of the restricted signed normal. -/
theorem canonicalLatitudeBandSignedNormal_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (canonicalLatitudeBandSignedNormal period hPeriod) :=
  (canonicalLatitudeCoverSignedNormal_contMDiff period hPeriod).comp
    contMDiff_subtype_val

/-- The inverse normal `arcsin x₀` is smooth on the open band. -/
theorem canonicalLatitudeBandArcsin_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : BandCover period hPeriod =>
        Real.arcsin (canonicalLatitudeBandSignedNormal period hPeriod point)) := by
  intro point
  have hLower :
      canonicalLatitudeBandSignedNormal period hPeriod point ≠ -1 := by
    have hBand := (abs_lt.mp point.2).1
    exact ne_of_gt hBand
  have hUpper :
      canonicalLatitudeBandSignedNormal period hPeriod point ≠ 1 := by
    have hBand := (abs_lt.mp point.2).2
    exact ne_of_lt hBand
  exact (Real.contDiffAt_arcsin hLower hUpper).contMDiffAt.comp point
    (canonicalLatitudeBandSignedNormal_contMDiff period hPeriod).contMDiffAt

/-- The positive normalization denominator is smooth on the open band. -/
theorem canonicalLatitudeBandCosArcsin_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : BandCover period hPeriod =>
        Real.cos (Real.arcsin
          (canonicalLatitudeBandSignedNormal period hPeriod point))) :=
  Real.contDiff_cos.contMDiff.comp
    (canonicalLatitudeBandArcsin_contMDiff period hPeriod)

/-- The normalization denominator is nonzero at every band point. -/
theorem canonicalLatitudeBandCosArcsin_ne_zero
    (point : BandCover period hPeriod) :
    Real.cos (Real.arcsin
      (canonicalLatitudeBandSignedNormal period hPeriod point)) ≠ 0 := by
  let spherePoint : EquatorialTubularBand :=
    ⟨point.1.fiber, point.2⟩
  exact (cos_equatorialTubularNormalInverse_pos spherePoint).ne'

/-- Normalized Euclidean tail on the open band. -/
def canonicalLatitudeCoverTubularTailOnBand
    (point : BandCover period hPeriod) : EuclideanR3 :=
  equatorialTubularTailInverse point.1.fiber

/-- Smoothness of the normalized Euclidean tail. -/
theorem canonicalLatitudeCoverTubularTailOnBand_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, EuclideanR3) ∞
      (canonicalLatitudeCoverTubularTailOnBand period hPeriod) := by
  have hCoordinates : ContMDiff coverModelWithCorners
      𝓘(Real, Fin 3 → Real) ∞
      (fun point : BandCover period hPeriod => fun index : Fin 3 =>
        point.1.fiber.1 index.succ /
          Real.cos (Real.arcsin
            (canonicalLatitudeBandSignedNormal period hPeriod point))) := by
    rw [contMDiff_pi_space]
    intro index
    have hNumerator : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point : BandCover period hPeriod =>
          point.1.fiber.1 index.succ) :=
      (canonicalLatitudeCoverSphereCoordinate_contMDiff
        period hPeriod index.succ).comp contMDiff_subtype_val
    exact hNumerator.div₀
      (canonicalLatitudeBandCosArcsin_contMDiff period hPeriod)
      (canonicalLatitudeBandCosArcsin_ne_zero period hPeriod)
  exact
    ((EuclideanSpace.equiv (Fin 3) Real).symm.toContinuousLinearMap.contMDiff.comp
      hCoordinates).congr fun point => rfl

/-- Standard two-sphere point defined by the normalized tail. -/
def canonicalLatitudeCoverTubularEquatorialBaseOnBand
    (point : BandCover period hPeriod) : StandardSphere2 :=
  equatorialTubularStandardBaseInverse
    ⟨point.1.fiber, point.2⟩

/-- The normalized-tail base is a smooth `S²`-valued map on the band. -/
theorem canonicalLatitudeCoverTubularEquatorialBaseOnBand_contMDiff :
    ContMDiff coverModelWithCorners (𝓡 2) ∞
      (canonicalLatitudeCoverTubularEquatorialBaseOnBand period hPeriod) := by
  letI : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩
  have hAmbient :=
    canonicalLatitudeCoverTubularTailOnBand_contMDiff period hPeriod
  have hSphere : ∀ point : BandCover period hPeriod,
      canonicalLatitudeCoverTubularTailOnBand period hPeriod point ∈
        Metric.sphere (0 : EuclideanR3) 1 := by
    intro point
    rw [Metric.mem_sphere, dist_zero_right]
    exact equatorialTubularTailInverse_norm ⟨point.1.fiber, point.2⟩
  exact (ContMDiff.codRestrict_sphere hAmbient hSphere).congr
    (fun point => rfl)

/-- Arbitrary fallback base, used only outside the open tubular band. -/
def canonicalLatitudeCoverTubularEquatorialBaseFallback : StandardSphere2 :=
  Classical.choice inferInstance

/-- Total normalized-tail base map.  Its value outside the band is irrelevant. -/
def canonicalLatitudeCoverTubularEquatorialBase
    (point : EffectiveCover period hPeriod) : StandardSphere2 :=
  if hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod then
    canonicalLatitudeCoverTubularEquatorialBaseOnBand period hPeriod
      ⟨point, hPoint⟩
  else
    canonicalLatitudeCoverTubularEquatorialBaseFallback

/-- The total base map is smooth at every point of the tubular band. -/
theorem canonicalLatitudeCoverTubularEquatorialBase_contMDiffAt
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    ContMDiffAt coverModelWithCorners (𝓡 2) ∞
      (canonicalLatitudeCoverTubularEquatorialBase period hPeriod) point := by
  let bandPoint : BandCover period hPeriod := ⟨point, hPoint⟩
  have hRestricted : ContMDiffAt coverModelWithCorners (𝓡 2) ∞
      (fun nearby : BandCover period hPeriod =>
        canonicalLatitudeCoverTubularEquatorialBase period hPeriod nearby.1)
      bandPoint := by
    apply
      (canonicalLatitudeCoverTubularEquatorialBaseOnBand_contMDiff
        period hPeriod).contMDiffAt.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun nearby => by
      simp [canonicalLatitudeCoverTubularEquatorialBase, nearby.2,
        canonicalLatitudeCoverTubularEquatorialBaseOnBand]
  exact (contMDiffAt_subtype_iff
    (U := canonicalLatitudeCoverTubularBandOpen period hPeriod)
    (f := canonicalLatitudeCoverTubularEquatorialBase period hPeriod)
    (x := bandPoint)).1 hRestricted

/-- Agreement with the algebraic normalized-tail inverse. -/
theorem canonicalLatitudeCoverTubularEquatorialBase_agrees
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    canonicalLatitudeCoverTubularEquatorialBase period hPeriod point =
      equatorialTwoSphereHomeomorph
        (equatorialTubularMapInverse ⟨point.fiber, hPoint⟩).1 := by
  simp [canonicalLatitudeCoverTubularEquatorialBase, hPoint,
    canonicalLatitudeCoverTubularEquatorialBaseOnBand,
    equatorialTubularMapInverse, equatorialTubularBaseInverse]

/-- The explicit normalized-tail map supplies the remaining cover-base
regularity package. -/
def canonicalLatitudeTubularEquatorialBaseRegularityData :
    CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod where
  base := canonicalLatitudeCoverTubularEquatorialBase period hPeriod
  smoothAt := canonicalLatitudeCoverTubularEquatorialBase_contMDiffAt
    period hPeriod
  agrees := canonicalLatitudeCoverTubularEquatorialBase_agrees
    period hPeriod

/-- Complete explicit tubular cover inverse regularity. -/
def canonicalLatitudeTubularCoverInverseRegularityData :
    CanonicalLatitudeTubularCoverInverseRegularityData
      period hPeriod :=
  (canonicalLatitudeTubularEquatorialBaseRegularityData period hPeriod)
    |>.toCoverInverseRegularityData

/-- The inverse-coordinate regularity input is completely discharged. -/
theorem canonicalLatitudeTubularCoverInverseRegularity_certificate :
    (∀ point : EffectiveCover period hPeriod,
      point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
        ContMDiffAt coverModelWithCorners
          canonicalLatitudeBaseModelWithCorners ∞
          (fun nearby =>
            ((canonicalLatitudeTubularCoverInverseRegularityData
              period hPeriod).parameter nearby).1) point) ∧
      (∀ point : EffectiveCover period hPeriod,
        point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
          ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
            (fun nearby =>
              ((canonicalLatitudeTubularCoverInverseRegularityData
                period hPeriod).parameter nearby).2.1) point) ∧
      (∀ point : EffectiveCover period hPeriod,
        point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
          canonicalLatitudeTubularPhysicalMap period hPeriod
              ((canonicalLatitudeTubularCoverInverseRegularityData
                period hPeriod).parameter point) =
            mappingTorusMk (sphereData period hPeriod) point) :=
  (canonicalLatitudeTubularEquatorialBaseRegularityData period hPeriod)
    |>.certificate

end
end P0EFTJanusMappingTorusEquatorialTubularCoverBaseRegularity4D
end JanusFormal

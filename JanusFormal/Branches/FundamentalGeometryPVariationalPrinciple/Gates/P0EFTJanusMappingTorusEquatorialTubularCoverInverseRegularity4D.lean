import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInverse4D

/-!
# Regularity of the explicit tubular cover inverse

The explicit inverse of the latitude map already reconstructs the non-polar
sphere point algebraically.  For the full mapping-torus cover, its time
coordinate is unchanged and its signed normal coordinate is `arcsin x₀`.

This file removes those two elementary regularity obligations.  It remains only
to provide the smooth `S²`-valued normalized-tail component on the open band.
From that component we construct a total tubular-parameter function, prove its
base and normal components smooth at every band point, and prove exact physical
reconstruction.  Hence it instantiates
`CanonicalLatitudeTubularCoverInverseRegularityData`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- The cover time coordinate is analytic. -/
theorem canonicalLatitudeCoverTime_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (MappingTorusCover.time : EffectiveCover period hPeriod → Real) := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞
    (coverHomeomorphProd (sphereData period hPeriod))
  exact (contMDiff_snd.comp hTo).congr fun point => rfl

/-- Explicit tubular parameter at a cover point known to lie in the open band. -/
def canonicalLatitudeTubularCoverParameterOnBand
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    CanonicalLatitudeTubularCollar :=
  let inverse := equatorialTubularMapInverse
    ⟨point.fiber, hPoint⟩
  ((equatorialTwoSphereHomeomorph inverse.1, point.time), inverse.2)

/-- The on-band parameter reconstructs the physical quotient point. -/
theorem canonicalLatitudeTubularCoverParameterOnBand_reconstruct
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    canonicalLatitudeTubularPhysicalMap period hPeriod
        (canonicalLatitudeTubularCoverParameterOnBand
          period hPeriod point hPoint) =
      mappingTorusMk (sphereData period hPeriod) point := by
  unfold canonicalLatitudeTubularCoverParameterOnBand
  let bandPoint : EquatorialTubularBand := ⟨point.fiber, hPoint⟩
  let inverse := equatorialTubularMapInverse bandPoint
  have hFiber : equatorialTubularMap inverse = point.fiber :=
    equatorialTubularMap_inverse bandPoint
  unfold canonicalLatitudeTubularPhysicalMap canonicalLatitudeTubularCoverMap
  apply congrArg (mappingTorusMk (sphereData period hPeriod))
  apply MappingTorusCover.ext
  · simpa [inverse, bandPoint, equatorialTubularMap] using hFiber
  · rfl

/-- The only remaining inverse-coordinate regularity input: a smooth standard
`S²` base which agrees on the band with the normalized-tail inverse. -/
structure CanonicalLatitudeTubularEquatorialBaseRegularityData where
  base : EffectiveCover period hPeriod → StandardSphere2
  smoothAt : ∀ point : EffectiveCover period hPeriod,
    point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
      ContMDiffAt coverModelWithCorners (𝓡 2) ∞ base point
  agrees : ∀ point : EffectiveCover period hPeriod,
    ∀ hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod,
      base point =
        equatorialTwoSphereHomeomorph
          (equatorialTubularMapInverse ⟨point.fiber, hPoint⟩).1

namespace CanonicalLatitudeTubularEquatorialBaseRegularityData

/-- An arbitrary fallback parameter used only outside the open band. -/
def fallbackParameter : CanonicalLatitudeTubularCollar :=
  Classical.choice inferInstance

/-- Total tubular parameter function.  On the open band it is the explicit
inverse; outside the band its value is irrelevant. -/
def parameter
    (baseData : CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod)
    (point : EffectiveCover period hPeriod) :
    CanonicalLatitudeTubularCollar :=
  if hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod then
    canonicalLatitudeTubularCoverParameterOnBand
      period hPeriod point hPoint
  else
    fallbackParameter period hPeriod

/-- Near a band point, the total parameter is the explicit inverse. -/
theorem parameter_eventuallyEq_onBand
    (baseData : CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod)
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    baseData.parameter =ᶠ[𝓝 point]
      fun nearby => canonicalLatitudeTubularCoverParameterOnBand
        period hPeriod nearby
        (show nearby ∈ canonicalLatitudeCoverTubularBand period hPeriod from
          Classical.decEq True ▸ hPoint) := by
  have hNeighborhood :=
    (canonicalLatitudeCoverTubularBand_isOpen period hPeriod).mem_nhds hPoint
  filter_upwards [hNeighborhood] with nearby hNearby
  simp [parameter, hNearby]

/-- The base component of the total inverse is smooth at every band point. -/
theorem parameter_base_contMDiffAt
    (baseData : CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod)
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    ContMDiffAt coverModelWithCorners
      canonicalLatitudeBaseModelWithCorners ∞
      (fun nearby => (baseData.parameter nearby).1) point := by
  have hBase : ContMDiffAt coverModelWithCorners (𝓡 2) ∞
      baseData.base point :=
    baseData.smoothAt point hPoint
  have hTime : ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (MappingTorusCover.time : EffectiveCover period hPeriod → Real) point :=
    (canonicalLatitudeCoverTime_contMDiff period hPeriod).contMDiffAt
  have hProduct : ContMDiffAt coverModelWithCorners
      canonicalLatitudeBaseModelWithCorners ∞
      (fun nearby => (baseData.base nearby, nearby.time)) point :=
    hBase.prodMk hTime
  apply hProduct.congr_of_eventuallyEq
  have hNeighborhood :=
    (canonicalLatitudeCoverTubularBand_isOpen period hPeriod).mem_nhds hPoint
  filter_upwards [hNeighborhood] with nearby hNearby
  simp [parameter, hNearby,
    canonicalLatitudeTubularCoverParameterOnBand,
    baseData.agrees nearby hNearby]

/-- The signed-normal component of the total inverse is smooth at every band
point. -/
theorem parameter_normal_contMDiffAt
    (baseData : CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod)
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (fun nearby => (baseData.parameter nearby).2.1) point := by
  let signed := canonicalLatitudeCoverSignedNormal period hPeriod
  have hLower : signed point ≠ -1 := by
    have := (abs_lt.mp hPoint).1
    exact ne_of_gt this
  have hUpper : signed point ≠ 1 := by
    have := (abs_lt.mp hPoint).2
    exact ne_of_lt this
  have hArcsin : ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (fun nearby => Real.arcsin (signed nearby)) point :=
    (Real.contDiffAt_arcsin hLower hUpper).contMDiffAt.comp point
      (canonicalLatitudeCoverSignedNormal_contMDiff period hPeriod).contMDiffAt
  apply hArcsin.congr_of_eventuallyEq
  have hNeighborhood :=
    (canonicalLatitudeCoverTubularBand_isOpen period hPeriod).mem_nhds hPoint
  filter_upwards [hNeighborhood] with nearby hNearby
  simp [parameter, hNearby,
    canonicalLatitudeTubularCoverParameterOnBand,
    equatorialTubularMapInverse,
    equatorialTubularNormalInverseSubtype,
    equatorialTubularNormalInverse, signed]

/-- Exact reconstruction by the total parameter on the open band. -/
theorem parameter_reconstruct
    (baseData : CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod)
    (point : EffectiveCover period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCoverTubularBand period hPeriod) :
    canonicalLatitudeTubularPhysicalMap period hPeriod
        (baseData.parameter point) =
      mappingTorusMk (sphereData period hPeriod) point := by
  simp [parameter, hPoint,
    canonicalLatitudeTubularCoverParameterOnBand_reconstruct]

/-- Instantiation of the complete cover-inverse regularity package. -/
def toCoverInverseRegularityData
    (baseData : CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod) :
    CanonicalLatitudeTubularCoverInverseRegularityData
      period hPeriod where
  parameter := baseData.parameter
  base_contMDiffAt := baseData.parameter_base_contMDiffAt
  normal_contMDiffAt := baseData.parameter_normal_contMDiffAt
  reconstruct := baseData.parameter_reconstruct

/-- Base-regularity reduction certificate. -/
theorem certificate
    (baseData : CanonicalLatitudeTubularEquatorialBaseRegularityData
      period hPeriod) :
    (∀ point : EffectiveCover period hPeriod,
      point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
        ContMDiffAt coverModelWithCorners
          canonicalLatitudeBaseModelWithCorners ∞
          (fun nearby => (baseData.parameter nearby).1) point) ∧
      (∀ point : EffectiveCover period hPeriod,
        point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
          ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
            (fun nearby => (baseData.parameter nearby).2.1) point) ∧
      (∀ point : EffectiveCover period hPeriod,
        point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
          canonicalLatitudeTubularPhysicalMap period hPeriod
              (baseData.parameter point) =
            mappingTorusMk (sphereData period hPeriod) point) :=
  ⟨baseData.parameter_base_contMDiffAt,
    baseData.parameter_normal_contMDiffAt,
    baseData.parameter_reconstruct⟩

end CanonicalLatitudeTubularEquatorialBaseRegularityData

end
end P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetLocalInverseReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D

/-!
# Physical tubular local inverses from a regular cover inverse

The projection from the reflected-sphere cover to the physical mapping torus is
an analytic local diffeomorphism.  Thus the only remaining tubular-coordinate
input may be placed upstairs.

A regular cover inverse assigns to every cover point a tubular parameter.  At
non-polar points its physical image is the quotient class of the original cover
point, and its base and normal components are smooth at that point.  Composing
this cover inverse with the canonical local inverse of the quotient projection
constructs a geometric local inverse at every physical tubular point.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set Topology Filter
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPolarOpenCover4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetLocalInverseReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Open non-polar band on the analytic cover. -/
def canonicalLatitudeCoverTubularBand :
    Set (EffectiveCover period hPeriod) :=
  {point | |canonicalLatitudeCoverSignedNormal period hPeriod point| < 1}

/-- The cover band is open. -/
theorem canonicalLatitudeCoverTubularBand_isOpen :
    IsOpen (canonicalLatitudeCoverTubularBand period hPeriod) := by
  unfold canonicalLatitudeCoverTubularBand
  exact isOpen_lt
    ((canonicalLatitudeCoverSignedNormal_contMDiff period hPeriod)
      |>.continuous.abs) continuous_const

/-- A total cover-level tubular parameter map, regular at every point of the
open non-polar band.  Its arbitrary values outside the band are irrelevant. -/
structure CanonicalLatitudeTubularCoverInverseRegularityData where
  parameter : EffectiveCover period hPeriod →
    CanonicalLatitudeTubularCollar period
  base_contMDiffAt : ∀ point : EffectiveCover period hPeriod,
    point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
      ContMDiffAt coverModelWithCorners
        canonicalLatitudeBaseModelWithCorners ∞
        (fun nearby => (parameter nearby).1) point
  normal_contMDiffAt : ∀ point : EffectiveCover period hPeriod,
    point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (fun nearby => (parameter nearby).2.1) point
  reconstruct : ∀ point : EffectiveCover period hPeriod,
    point ∈ canonicalLatitudeCoverTubularBand period hPeriod →
      canonicalLatitudeTubularPhysicalMap period hPeriod (parameter point) =
        mappingTorusMk (sphereData period hPeriod) point

namespace CanonicalLatitudeTubularCoverInverseRegularityData

/-- Membership of a physical tubular point gives a band representative upstairs. -/
theorem representative_mem_band
    (inverseData : CanonicalLatitudeTubularCoverInverseRegularityData
      period hPeriod)
    (point : EffectiveCover period hPeriod)
    (hPoint : mappingTorusMk (sphereData period hPeriod) point ∈
      canonicalLatitudeCauchyJetTubularRegion period hPeriod) :
    point ∈ canonicalLatitudeCoverTubularBand period hPeriod := by
  change canonicalLatitudeQuotientNormalSquare period hPeriod
      (mappingTorusMk (sphereData period hPeriod) point) < 1 at hPoint
  rw [canonicalLatitudeQuotientNormalSquare_mk] at hPoint
  change |canonicalLatitudeCoverSignedNormal period hPeriod point| < 1
  have hAbsNonnegative :
      0 ≤ |canonicalLatitudeCoverSignedNormal period hPeriod point| := abs_nonneg _
  have hAbsSquare :
      |canonicalLatitudeCoverSignedNormal period hPeriod point| ^ 2 < 1 := by
    simpa [sq_abs] using hPoint
  nlinarith

/-- Construct the physical local inverse based at one selected cover
representative. -/
def localInverseAtRepresentative
    (inverseData : CanonicalLatitudeTubularCoverInverseRegularityData
      period hPeriod)
    (point : EffectiveCover period hPeriod)
    (hPoint : mappingTorusMk (sphereData period hPeriod) point ∈
      canonicalLatitudeCauchyJetTubularRegion period hPeriod) :
    CanonicalLatitudeTubularPhysicalLocalInverseAt period hPeriod
      (mappingTorusMk (sphereData period hPeriod) point) := by
  let projection := mappingTorusMk (sphereData period hPeriod)
  have hProjection : IsLocalDiffeomorph coverModelWithCorners
      coverModelWithCorners ω projection :=
    reflectedSphere_projection_isLocalDiffeomorph period hPeriod
  let localDiffeomorph := hProjection point
  let inverseSection := localDiffeomorph.localInverse
  have hBand : point ∈ canonicalLatitudeCoverTubularBand period hPeriod :=
    inverseData.representative_mem_band period hPeriod point hPoint
  have hSectionPoint : inverseSection (projection point) = point :=
    localDiffeomorph.localInverse_left_inv
      localDiffeomorph.localInverse_mem_target
  have hSectionSmooth : ContMDiffAt coverModelWithCorners
      coverModelWithCorners ∞ inverseSection (projection point) :=
    localDiffeomorph.localInverse_contMDiffAt.of_le (by simp)
  have hSectionBand : ∀ᶠ nearby in 𝓝 (projection point),
      inverseSection nearby ∈ canonicalLatitudeCoverTubularBand period hPeriod := by
    apply hSectionSmooth.continuousAt.preimage_mem_nhds
    rw [hSectionPoint]
    exact (canonicalLatitudeCoverTubularBand_isOpen period hPeriod).mem_nhds hBand
  refine
    { parameter := fun nearby => inverseData.parameter (inverseSection nearby)
      base_contMDiffAt := ?_
      normal_contMDiffAt := ?_
      right_inverse := ?_ }
  · have hBase : ContMDiffAt coverModelWithCorners
        canonicalLatitudeBaseModelWithCorners ∞
        (fun nearby => (inverseData.parameter nearby).1)
        (inverseSection (projection point)) := by
      rw [hSectionPoint]
      exact inverseData.base_contMDiffAt point hBand
    exact hBase.comp (projection point) hSectionSmooth
  · have hNormal : ContMDiffAt coverModelWithCorners
        𝓘(Real, Real) ∞
        (fun nearby => (inverseData.parameter nearby).2.1)
        (inverseSection (projection point)) := by
      rw [hSectionPoint]
      exact inverseData.normal_contMDiffAt point hBand
    exact hNormal.comp (projection point) hSectionSmooth
  · filter_upwards [hSectionBand,
      localDiffeomorph.localInverse_eventuallyEq_right]
      with nearby hNearbyBand hRight
    calc
      canonicalLatitudeTubularPhysicalMap period hPeriod
          (inverseData.parameter (inverseSection nearby)) =
        projection (inverseSection nearby) :=
          inverseData.reconstruct (inverseSection nearby) hNearbyBand
      _ = nearby := by simpa [Function.comp_def] using hRight

/-- The cover inverse constructs local inverses at every physical tubular point. -/
def toPhysicalLocalInverseData
    (inverseData : CanonicalLatitudeTubularCoverInverseRegularityData
      period hPeriod) :
    CanonicalLatitudeTubularPhysicalLocalInverseData period hPeriod where
  localInverseAt := by
    intro quotientPoint hQuotientPoint
    let coverPoint := Classical.choose
      (mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint)
    have hCoverPoint := Classical.choose_spec
      (mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint)
    rw [← hCoverPoint] at hQuotientPoint ⊢
    exact inverseData.localInverseAtRepresentative period hPeriod
      coverPoint hQuotientPoint

/-- Cover regularity and smooth boundary cores install the complete smooth
candidate extension. -/
def toCandidateExtensionData
    {ValueCore NormalCore : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (inverseData : CanonicalLatitudeTubularCoverInverseRegularityData
      period hPeriod)
    (smoothCore :
      P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D.CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
        period ValueCore NormalCore) :=
  (inverseData.toPhysicalLocalInverseData period hPeriod)
    |>.toCandidateExtensionData period hPeriod smoothCore

/-- Cover-inverse reduction certificate. -/
theorem certificate
    {ValueCore NormalCore : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (inverseData : CanonicalLatitudeTubularCoverInverseRegularityData
      period hPeriod)
    (smoothCore :
      P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D.CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
        period ValueCore NormalCore) :
    (∀ data : ValueCore × NormalCore,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (smoothCore.core.candidate period hPeriod data)) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) :=
  (inverseData.toPhysicalLocalInverseData period hPeriod)
    |>.certificate period hPeriod smoothCore

end CanonicalLatitudeTubularCoverInverseRegularityData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D
end JanusFormal

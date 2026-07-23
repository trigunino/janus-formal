import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D

/-!
# Physical tubular local inverses for the scalar Cauchy jet

A local right inverse of the physical tubular map supplies the signed base and
normal coordinates required by the tubular-chart smoothness reduction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetLocalInverseReduction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set Topology Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalCandidate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPolarOpenCover4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The global candidate agrees with its local formula on the physical tubular
map. -/
theorem canonicalLatitudeCauchyJetGlobalCandidate_tubularPhysicalMap
    (data : CanonicalLatitudeDeckCauchyData period)
    (parameter : CanonicalLatitudeTubularCollar period) :
    canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data
        (canonicalLatitudeTubularPhysicalMap period hPeriod parameter) =
      canonicalLatitudeLocalCauchyExtension
        (data.value, data.normal) (parameter.1, parameter.2.1) := by
  simpa [CanonicalLatitudeDeckCauchyData.tubularLocalExtension,
    CanonicalLatitudeDeckCauchyData.localExtension] using
    P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalCandidate4D.canonicalLatitudeCauchyJetGlobalCandidate_tubular
      period hPeriod data parameter

/-- Smooth local signed coordinates that right-invert the physical tubular map
near one point. -/
structure CanonicalLatitudeTubularPhysicalLocalInverseAt
    (point : EffectiveQuotient period hPeriod) where
  parameter : EffectiveQuotient period hPeriod →
    CanonicalLatitudeTubularCollar period
  base_contMDiffAt : ContMDiffAt coverModelWithCorners
    canonicalLatitudeBaseModelWithCorners ∞
      (fun nearby => (parameter nearby).1) point
  normal_contMDiffAt : ContMDiffAt coverModelWithCorners
    𝓘(Real, Real) ∞ (fun nearby => (parameter nearby).2.1) point
  right_inverse : ∀ᶠ nearby in 𝓝 point,
    canonicalLatitudeTubularPhysicalMap period hPeriod (parameter nearby) = nearby

namespace CanonicalLatitudeTubularPhysicalLocalInverseAt

/-- A physical local inverse gives the local chart used by the smoothness
reduction. -/
def toLocalChartAt
    {point : EffectiveQuotient period hPeriod}
    (localInverse : CanonicalLatitudeTubularPhysicalLocalInverseAt
      period hPeriod point) :
    CanonicalLatitudeCauchyJetLocalChartAt period hPeriod point where
  base := fun nearby => (localInverse.parameter nearby).1
  normal := fun nearby => (localInverse.parameter nearby).2.1
  base_contMDiffAt := localInverse.base_contMDiffAt
  normal_contMDiffAt := localInverse.normal_contMDiffAt
  candidate_eventuallyEq := by
    intro data
    filter_upwards [localInverse.right_inverse] with nearby hNearby
    calc
      canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data nearby =
          canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data
            (canonicalLatitudeTubularPhysicalMap period hPeriod
              (localInverse.parameter nearby)) :=
        congrArg (canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data)
          hNearby.symm
      _ = canonicalLatitudeLocalCauchyExtension
          (data.value, data.normal)
          ((localInverse.parameter nearby).1,
            (localInverse.parameter nearby).2.1) :=
        canonicalLatitudeCauchyJetGlobalCandidate_tubularPhysicalMap
          period hPeriod data (localInverse.parameter nearby)

end CanonicalLatitudeTubularPhysicalLocalInverseAt

/-- A physical local inverse at every non-polar point. -/
structure CanonicalLatitudeTubularPhysicalLocalInverseData where
  localInverseAt : ∀ point : EffectiveQuotient period hPeriod,
    point ∈ canonicalLatitudeCauchyJetTubularRegion period hPeriod →
      CanonicalLatitudeTubularPhysicalLocalInverseAt period hPeriod point

namespace CanonicalLatitudeTubularPhysicalLocalInverseData

/-- Convert physical local inverses to the tubular atlas package. -/
def toTubularAtlasData
    (inverseData : CanonicalLatitudeTubularPhysicalLocalInverseData
      period hPeriod) :
    CanonicalLatitudeCauchyJetTubularAtlasData period hPeriod where
  chartAt := fun point hPoint =>
    (inverseData.localInverseAt point hPoint).toLocalChartAt period hPeriod

/-- Install the complete smooth candidate extension. -/
def toCandidateExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (inverseData : CanonicalLatitudeTubularPhysicalLocalInverseData
      period hPeriod)
    (smoothCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore) :=
  (inverseData.toTubularAtlasData period hPeriod)
    |>.toCandidateExtensionData period hPeriod smoothCore

/-- Physical-local-inverse reduction certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (inverseData : CanonicalLatitudeTubularPhysicalLocalInverseData
      period hPeriod)
    (smoothCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore) :
    (∀ data : ValueCore × NormalCore,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (smoothCore.core.candidate period hPeriod data)) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) :=
  (inverseData.toTubularAtlasData period hPeriod)
    |>.certificate period hPeriod smoothCore

end CanonicalLatitudeTubularPhysicalLocalInverseData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetLocalInverseReduction4D
end JanusFormal

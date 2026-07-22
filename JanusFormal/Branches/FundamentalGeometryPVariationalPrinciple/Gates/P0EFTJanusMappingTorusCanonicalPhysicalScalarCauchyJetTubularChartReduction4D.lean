import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPolarOpenCover4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeSmoothCauchyJet4D

/-!
# Tubular Cauchy smoothness from local inverse charts

The remaining smoothness question is local on the non-polar tubular region.
Around every point, choose a smooth base coordinate and a smooth signed normal
coordinate such that the global candidate agrees locally with the explicit
Cauchy formula

`eta(nu) g(base) + nu eta(nu) h(base)`.

For smooth periodic value representatives and smooth antiperiodic normal
representatives, the local formula is already jointly `C∞`.  Composition with
these local coordinates and congruence on a neighborhood prove tubular
smoothness, hence global smoothness by the canonical tubular--polar open cover.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open Set Topology Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothCauchyJet4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalCandidate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetOpenCoverSmoothness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPolarOpenCover4D

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

/-- Boundary-core data with smooth value and normal representatives. -/
structure CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    extends CanonicalPhysicalScalarCauchyJetBoundaryCoreData
      period ValueCore NormalCore where
  value_contMDiff : ∀ value : ValueCore,
    ContMDiff canonicalLatitudeBaseModelWithCorners 𝓘(Real, Real) ∞
      (toCanonicalPhysicalScalarCauchyJetBoundaryCoreData.valueRepresentative
        value)
  normal_contMDiff : ∀ normal : NormalCore,
    ContMDiff canonicalLatitudeBaseModelWithCorners 𝓘(Real, Real) ∞
      (toCanonicalPhysicalScalarCauchyJetBoundaryCoreData.normalRepresentative
        normal)

namespace CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData

/-- Underlying nonsmoothness-independent boundary-core package. -/
def core
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (smoothCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore) :
    CanonicalPhysicalScalarCauchyJetBoundaryCoreData
      period ValueCore NormalCore :=
  smoothCore.toCanonicalPhysicalScalarCauchyJetBoundaryCoreData

/-- Smooth deck-compatible data associated to a boundary-core pair. -/
def smoothDeckData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (smoothCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    SmoothCanonicalLatitudeDeckCauchyData period where
  toCanonicalLatitudeDeckCauchyData := smoothCore.core.deckData data
  value_contMDiff := smoothCore.value_contMDiff data.1
  normal_contMDiff := smoothCore.normal_contMDiff data.2

end CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData

/-- Local signed tubular coordinates around one physical point.  The candidate
agreement is stated for arbitrary deck-compatible Cauchy data, so the geometry
is independent of the chosen boundary cores. -/
structure CanonicalLatitudeCauchyJetLocalChartAt
    (point : EffectiveQuotient period hPeriod) where
  base : EffectiveQuotient period hPeriod → CanonicalLatitudeBase
  normal : EffectiveQuotient period hPeriod → Real
  base_contMDiffAt : ContMDiffAt coverModelWithCorners
    canonicalLatitudeBaseModelWithCorners ∞ base point
  normal_contMDiffAt : ContMDiffAt coverModelWithCorners
    𝓘(Real, Real) ∞ normal point
  candidate_eventuallyEq : ∀ data : CanonicalLatitudeDeckCauchyData period,
    canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data =ᶠ[𝓝 point]
      fun nearby =>
        canonicalLatitudeLocalCauchyExtension
          (data.value, data.normal) (base nearby, normal nearby)

/-- A local inverse chart at every point of the canonical tubular region. -/
structure CanonicalLatitudeCauchyJetTubularAtlasData where
  chartAt : ∀ point : EffectiveQuotient period hPeriod,
    point ∈ canonicalLatitudeCauchyJetTubularRegion period hPeriod →
      CanonicalLatitudeCauchyJetLocalChartAt period hPeriod point

namespace CanonicalLatitudeCauchyJetLocalChartAt

/-- Smooth boundary data make the local chart expression smooth. -/
theorem localExpression_contMDiffAt
    (chart : CanonicalLatitudeCauchyJetLocalChartAt period hPeriod point)
    (data : SmoothCanonicalLatitudeDeckCauchyData period) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (fun nearby =>
        canonicalLatitudeLocalCauchyExtension
          (data.value, data.normal)
          (chart.base nearby, chart.normal nearby)) point := by
  have hParameter : ContMDiffAt coverModelWithCorners
      canonicalLatitudeParameterModelWithCorners ∞
      (fun nearby => (chart.base nearby, chart.normal nearby)) point :=
    chart.base_contMDiffAt.prodMk chart.normal_contMDiffAt
  exact data.localExtension_contMDiff.contMDiffAt.comp point hParameter

/-- Candidate smoothness at the center of one local tubular chart. -/
theorem candidate_contMDiffAt
    (chart : CanonicalLatitudeCauchyJetLocalChartAt period hPeriod point)
    (data : SmoothCanonicalLatitudeDeckCauchyData period) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data) point :=
  (chart.localExpression_contMDiffAt data).congr_of_eventuallyEq
    (chart.candidate_eventuallyEq data).symm

end CanonicalLatitudeCauchyJetLocalChartAt

namespace CanonicalLatitudeCauchyJetTubularAtlasData

/-- Local inverse charts prove tubular smoothness for every smooth deck datum. -/
theorem candidate_contMDiffAt
    (atlas : CanonicalLatitudeCauchyJetTubularAtlasData period hPeriod)
    (data : SmoothCanonicalLatitudeDeckCauchyData period)
    (point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ canonicalLatitudeCauchyJetTubularRegion period hPeriod) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data) point :=
  (atlas.chartAt point hPoint).candidate_contMDiffAt data

/-- Convert smooth boundary cores and the local atlas to the sole tubular
smoothness package required by the polar open-cover theorem. -/
def toTubularSmoothnessData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (atlas : CanonicalLatitudeCauchyJetTubularAtlasData period hPeriod)
    (smoothCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore) :
    CanonicalPhysicalScalarCauchyJetTubularSmoothnessData
      period hPeriod ValueCore NormalCore where
  core := smoothCore.core
  tubular_smoothAt := by
    intro data point hPoint
    exact atlas.candidate_contMDiffAt
      (smoothCore.smoothDeckData data) point hPoint

/-- Install the complete globally smooth candidate extension. -/
def toCandidateExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (atlas : CanonicalLatitudeCauchyJetTubularAtlasData period hPeriod)
    (smoothCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore) :=
  (atlas.toTubularSmoothnessData smoothCore).toCandidateExtensionData

/-- Tubular-chart reduction certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (atlas : CanonicalLatitudeCauchyJetTubularAtlasData period hPeriod)
    (smoothCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore) :
    (∀ data : ValueCore × NormalCore,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (smoothCore.core.candidate hPeriod data)) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) :=
  (atlas.toTubularSmoothnessData smoothCore).certificate

end CanonicalLatitudeCauchyJetTubularAtlasData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D
end JanusFormal

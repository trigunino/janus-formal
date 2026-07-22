import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D

/-!
# Canonical Cauchy-jet physical Green core

The value and normal boundary cores are now fixed canonical types.  Their deck
laws, smoothness, square integrability, `L²` embeddings and almost-everywhere
representatives are definitions rather than fields.

Consequently the concrete physical Green core requires only:

* density of the canonical periodic and antiperiodic core embeddings;
* smoothness of the normalized equatorial-tail inverse;
* globalization of the wave operator;
* the Euler-skew/divergence integral theorem.

The explicit global Cauchy jet and all of its trace identities are then
constructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period
private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Canonical boundary and tubular data for the physical smooth Green core. -/
structure CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
    (massSquared : Real) where
  globalization : CanonicalPhysicalScalarWaveGlobalizationData
    period hPeriod massSquared
  boundaryDensity : CanonicalLatitudeSmoothBoundaryCoreDensityData period
  tubularBase : CanonicalLatitudeTubularEquatorialBaseRegularityData
    period hPeriod
  integral_eq_divergence :
    ∀ field test : SmoothQuotientField period hPeriod Real,
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData

/-- Complete regular inverse of the non-polar tubular cover coordinates. -/
def tubularInverse
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared) :=
  canonical.tubularBase.toCoverInverseRegularityData

/-- Canonical smooth boundary-core data. -/
def boundaryCore
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared) :=
  canonical.boundaryDensity.toSmoothCauchyJetBoundaryCoreData

/-- Conversion to the general explicit-Cauchy geometric package. -/
def toCauchyJetGeometricData
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared (ValueCore period) (NormalCore period) where
  globalization := canonical.globalization
  boundaryCore := canonical.boundaryCore
  tubularInverse := canonical.tubularInverse
  integral_eq_divergence := canonical.integral_eq_divergence

/-- Explicit globally smooth Cauchy extension. -/
def extension
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared) :=
  canonical.toCauchyJetGeometricData.extension

/-- Correct dense physical scalar Green core. -/
def greenCore
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared) :=
  canonical.toCauchyJetGeometricData.greenCore

/-- Exact paired Cauchy trace of the canonical extension. -/
theorem cauchyTrace_extension
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared)
    (data : ValueCore period × NormalCore period) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
        period hPeriod (canonical.extension data) =
      P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D.canonicalScalarBoundaryCorePairEmbedding
        (canonicalLatitudeSmoothPeriodicValueEmbedding period)
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)
        data :=
  canonical.toCauchyJetGeometricData.cauchyTrace_extension data

/-- Density of the physical smooth Cauchy trace. -/
theorem boundaryTrace_denseRange
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared) :
    DenseRange
      (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
        period hPeriod) :=
  canonical.toCauchyJetGeometricData.boundaryTrace_denseRange

/-- Canonical Green-core certificate. -/
theorem certificate
    (canonical : CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData
      period hPeriod massSquared) :
    DenseRange
        (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      (∀ data : ValueCore period × NormalCore period,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
            period hPeriod (canonical.extension data) =
          P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D.canonicalScalarBoundaryCorePairEmbedding
            (canonicalLatitudeSmoothPeriodicValueEmbedding period)
            (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)
            data) :=
  ⟨canonical.boundaryDensity.valueDense,
    canonical.boundaryDensity.normalDense,
    canonical.boundaryTrace_denseRange,
    canonical.cauchyTrace_extension⟩

end CanonicalPhysicalScalarCanonicalCauchyJetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetGreenCore4D
end JanusFormal

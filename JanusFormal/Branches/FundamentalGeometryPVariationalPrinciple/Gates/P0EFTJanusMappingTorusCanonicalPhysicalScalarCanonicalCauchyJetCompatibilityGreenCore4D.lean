import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverBaseRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D

/-!
# Canonical explicit Cauchy-jet Green core from Euler compatibility

The normalized-tail tubular inverse is now explicit and smooth.  Therefore the
canonical physical scalar Green core no longer needs a tubular-coordinate
regularity field.

Its remaining inputs are exactly:

* overlap compatibility of the physical Euler residual;
* density of the canonical smooth periodic and antiperiodic boundary cores;
* the global Euler-skew/divergence integral identity.

The canonical smooth boundary cores provide all deck laws, smoothness,
integrability and `L²` embeddings.  The explicit normalized-tail theorem provides
the global smooth Cauchy extension.  Together these data construct the genuine
physical bulk operator, the dense smooth Cauchy trace and the exact Green
identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusEquatorialTubularCoverBaseRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period
private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Canonical compatibility-based Green-core data with the tubular inverse
already discharged. -/
structure CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
    (massSquared : Real) where
  eulerCompatibility : CanonicalPhysicalScalarEulerCompatibilityData
    period hPeriod massSquared
  boundaryDensity : CanonicalLatitudeSmoothBoundaryCoreDensityData period
  integral_eq_divergence :
    ∀ field test : SmoothQuotientField period hPeriod Real,
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData

/-- Canonical smooth periodic/antiperiodic boundary package. -/
def boundaryCore
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :=
  data.boundaryDensity.toSmoothCauchyJetBoundaryCoreData

/-- Explicit smooth tubular inverse, now a theorem. -/
def tubularInverse
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :=
  canonicalLatitudeTubularCoverInverseRegularityData period hPeriod

/-- Conversion to the general compatibility-based explicit-Cauchy package. -/
def toCompatibilityData
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared (ValueCore period) (NormalCore period) where
  eulerCompatibility := data.eulerCompatibility
  boundaryCore := data.boundaryCore
  tubularInverse := data.tubularInverse
  integral_eq_divergence := data.integral_eq_divergence

/-- Explicit global smooth Cauchy extension. -/
def extension
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :=
  (data.toCompatibilityData period hPeriod).extension period hPeriod

/-- Genuine physical bulk operator. -/
def operatorData
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :=
  (data.toCompatibilityData period hPeriod).operatorData period hPeriod

/-- Correct dense physical scalar Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :=
  (data.toCompatibilityData period hPeriod).greenCore period hPeriod

/-- Exact canonical Cauchy trace of the explicit extension. -/
theorem cauchyTrace_extension
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared)
    (boundary : ValueCore period × NormalCore period) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
        period hPeriod (data.extension period hPeriod boundary) =
      canonicalScalarBoundaryCorePairEmbedding
        (canonicalLatitudeSmoothPeriodicValueEmbedding period)
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)
        boundary :=
  (data.toCompatibilityData period hPeriod).cauchyTrace_extension
    period hPeriod boundary

/-- Density of the physical smooth Cauchy trace. -/
theorem boundaryTrace_denseRange
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :
    DenseRange
      (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
        period hPeriod) :=
  (data.toCompatibilityData period hPeriod).boundaryTrace_denseRange
    period hPeriod

/-- Exact physical Green identity. -/
theorem green_identity
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared)
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real ((data.greenCore period hPeriod).core.operator field)
          ((data.greenCore period hPeriod).core.inclusion test) -
        inner Real ((data.greenCore period hPeriod).core.inclusion field)
          ((data.greenCore period hPeriod).core.operator test) =
      2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
        ((data.greenCore period hPeriod).core.boundaryTrace field)
        ((data.greenCore period hPeriod).core.boundaryTrace test) :=
  (data.toCompatibilityData period hPeriod).green_identity
    period hPeriod field test

/-- Canonical compatibility Green-core certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      (∀ boundary : ValueCore period × NormalCore period,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
            period hPeriod (data.extension period hPeriod boundary) =
          canonicalScalarBoundaryCorePairEmbedding
            (canonicalLatitudeSmoothPeriodicValueEmbedding period)
            (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)
            boundary) ∧
      (∀ field test : SmoothQuotientField period hPeriod Real,
        inner Real ((data.greenCore period hPeriod).core.operator field)
              ((data.greenCore period hPeriod).core.inclusion test) -
            inner Real ((data.greenCore period hPeriod).core.inclusion field)
              ((data.greenCore period hPeriod).core.operator test) =
          2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
            ((data.greenCore period hPeriod).core.boundaryTrace field)
            ((data.greenCore period hPeriod).core.boundaryTrace test)) :=
  ⟨data.boundaryDensity.valueDense,
    data.boundaryDensity.normalDense,
    data.boundaryTrace_denseRange period hPeriod,
    data.cauchyTrace_extension period hPeriod,
    data.green_identity period hPeriod⟩

end CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D
end JanusFormal

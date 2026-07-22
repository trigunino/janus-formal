import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedCauchyJetGreenCore4D

/-!
# Canonical Cauchy-jet Green core from the open fundamental strip

The source of the physical parametrization is fixed to round `S³` times the
interior of one fundamental time interval.  Its measure is explicit,
open-positive and measure-preserving, and its physical image is now proved
dense.  Thus physical full support and Euler `L²` faithfulness are theorems.

The remaining Green-core inputs are only:

* overlap compatibility of the physical Euler residual;
* density of the canonical smooth periodic and antiperiodic boundary cores;
* the global Euler-skew/divergence integral identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedCauchyJetGreenCore4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period
private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Canonical Green-core data after closing physical full support. -/
structure CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
    (massSquared : Real) where
  euler : CanonicalPhysicalScalarEulerCompatibilityOnlyData
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

namespace CanonicalPhysicalScalarCanonicalInteriorCauchyJetData

/-- Conversion to the generic dense-parametrized canonical Green-core package. -/
def toDenseParametrizedCauchyJetData
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalDenseParametrizedCauchyJetData
      period hPeriod
      (CanonicalLorentzInteriorParameter period)
      (canonicalLorentzInteriorMeasure period)
      massSquared where
  parameterization :=
    (canonicalLorentzInteriorDenseRangeData period hPeriod)
      |>.toEulerDenseParametrizationData
  euler := data.euler
  boundaryDensity := data.boundaryDensity
  integral_eq_divergence := data.integral_eq_divergence

/-- Conversion to the canonical compatibility-based Cauchy-jet package. -/
def toCanonicalCauchyJetCompatibilityData
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :=
  data.toDenseParametrizedCauchyJetData.toCanonicalCauchyJetCompatibilityData

/-- Full support of the physical Lorentz volume. -/
def physicalMeasureOpenPositive
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
      period hPeriod).IsOpenPosMeasure :=
  data.toDenseParametrizedCauchyJetData.physicalMeasureOpenPositive

/-- Explicit global smooth Cauchy extension. -/
def extension
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :=
  data.toDenseParametrizedCauchyJetData.extension

/-- Genuine faithful physical Euler operator. -/
def operatorData
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :=
  data.toDenseParametrizedCauchyJetData.operatorData

/-- Correct dense physical scalar Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :=
  data.toDenseParametrizedCauchyJetData.greenCore

/-- Open-fundamental-strip Green-core certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) ∧
      (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).IsOpenPosMeasure ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      (∀ boundary : ValueCore period × NormalCore period,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
            period hPeriod (data.extension boundary) =
          canonicalScalarBoundaryCorePairEmbedding
            (canonicalLatitudeSmoothPeriodicValueEmbedding period)
            (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)
            boundary) :=
  ⟨canonicalLorentzInteriorPhysicalMap_denseRange period hPeriod,
    data.physicalMeasureOpenPositive,
    data.toCanonicalCauchyJetCompatibilityData.boundaryTrace_denseRange,
    data.toCanonicalCauchyJetCompatibilityData.cauchyTrace_extension⟩

end CanonicalPhysicalScalarCanonicalInteriorCauchyJetData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedApproximation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedCauchyJetGreenCore4D

/-!
# Canonical Cauchy-jet Green core on the physical mapping torus

Full support of the physical Lorentz volume is a theorem.  Density of the
periodic value core and antiperiodic normal core is also a theorem, generated
from the single dense core of smooth interior-supported seeds.

The remaining Green-core inputs are exactly:

* overlap compatibility of the physical Euler residual;
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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedDensityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedApproximation4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedCauchyJetGreenCore4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period
private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Canonical physical Green-core data after closing measure full support and
both boundary-core density theorems. -/
structure CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
    (massSquared : Real) where
  euler : CanonicalPhysicalScalarEulerCompatibilityOnlyData
    period hPeriod massSquared
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

/-- Unconditional common interior-seed density. -/
def boundarySeedDensity
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    CanonicalLatitudeSmoothInteriorSeedDensityData period :=
  (canonicalLatitudeContinuousInteriorSeedApproximationData period hPeriod)
    |>.toInteriorSeedDensityData

/-- Unconditional periodic and antiperiodic boundary densities. -/
def boundaryDensity
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    CanonicalLatitudeSmoothBoundaryCoreDensityData period :=
  canonicalLatitudeSmoothBoundaryCoreDensityData period hPeriod

/-- Direct conversion to the canonical compatibility-based Cauchy-jet package. -/
def toCanonicalCauchyJetCompatibilityData
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared where
  eulerCompatibility := data.euler.toCanonicalCompatibilityData period hPeriod
  boundaryDensity := data.boundaryDensity
  integral_eq_divergence := data.integral_eq_divergence

/-- Compatibility conversion through the generic dense-parametrized layer. -/
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

/-- Full support of the physical Lorentz volume. -/
def physicalMeasureOpenPositive
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
      period hPeriod).IsOpenPosMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod

/-- Explicit global smooth Cauchy extension. -/
def extension
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalCauchyJetCompatibilityData.extension

/-- Genuine faithful physical Euler operator. -/
def operatorData
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalCauchyJetCompatibilityData.operatorData

/-- Correct dense physical scalar Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalCauchyJetCompatibilityData.greenCore

/-- Canonical physical Green-core certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared) :
    DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) ∧
      (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).IsOpenPosMeasure ∧
      DenseRange (canonicalLatitudeSmoothInteriorSeedEmbedding period) ∧
      DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) ∧
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
    intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod,
    canonicalLatitudeSmoothInteriorSeedEmbedding_denseRange period hPeriod,
    data.boundaryDensity.valueDense,
    data.boundaryDensity.normalDense,
    data.toCanonicalCauchyJetCompatibilityData.boundaryTrace_denseRange,
    data.toCanonicalCauchyJetCompatibilityData.cauchyTrace_extension⟩

end CanonicalPhysicalScalarCanonicalInteriorCauchyJetData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D
end JanusFormal

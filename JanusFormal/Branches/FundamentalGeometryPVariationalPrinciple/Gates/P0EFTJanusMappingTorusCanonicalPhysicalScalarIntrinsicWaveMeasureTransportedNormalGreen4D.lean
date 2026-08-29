import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalGreen4D

/-!
# Intrinsic Green data from one normal pushforward measure identity

The full normal transport interface is generated from

`Measure.map transport μ_fullNormal = 2 • μ_positiveCollar`.

This file carries that single geometric equality to the intrinsic scalar Green
core.  The normal density, its integrability and its exact `-2` integral are all
constructed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreen4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalHalfCollarTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalGreen4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Intrinsic-wave Green data whose normal transport is specified solely by its
pushforward measure. -/
structure CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData
    (massSquared : Real) where
  intrinsicWave : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod
  measureTransport :
    CanonicalLatitudeNormalToHalfCollarMeasureTransportData period
  halfCollarDivergence_integrable :
    ∀ field test : SmoothScalarField period hPeriod,
      Integrable
        (canonicalPhysicalScalarHalfCollarDivergenceDensity
          period hPeriod massSquared field test)
        (canonicalLatitudeCollarMeasure period)
  tangential_base_integral_zero :
    ∀ field test normal,
      (∫ base,
        (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test (base, normal) +
          canonicalPhysicalScalarHalfCollarDivergenceDensity
            period hPeriod massSquared field test
            (measureTransport.transport (base, normal)))
        ∂canonicalLatitudeBaseMeasure period) = 0

namespace CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData

/-- Conversion to the analytical transported-normal Green interface. -/
def toTransportedNormalGreenData
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveTransportedNormalGreenData
      period hPeriod massSquared where
  intrinsicWave := data.intrinsicWave
  transportData := data.measureTransport.toNormalToHalfCollarTransportData period
  halfCollarDivergence_integrable := data.halfCollarDivergence_integrable
  tangential_base_integral_zero := data.tangential_base_integral_zero

/-- Transport-generated normal Green density. -/
def normalDensity
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData
      period hPeriod massSquared) :=
  (data.toTransportedNormalGreenData period hPeriod).normalDensity period hPeriod

/-- Conversion to the smallest canonical-normal Green package. -/
def toCanonicalNormalGreenData
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData
      period hPeriod massSquared) :=
  (data.toTransportedNormalGreenData period hPeriod).toCanonicalNormalGreenData
    period hPeriod

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData
      period hPeriod massSquared) :=
  (data.toCanonicalNormalGreenData period hPeriod).greenCore period hPeriod

/-- Measure-transport intrinsic Green certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData
      period hPeriod massSquared) :
    Measure.map data.measureTransport.transport
        (canonicalLatitudeCauchyJetProductMeasure period) =
      (2 : NNReal) • canonicalLatitudeCollarMeasure period ∧
      (∀ field test,
        Integrable (data.normalDensity period hPeriod field test)
          (canonicalLatitudeCauchyJetProductMeasure period)) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.measureTransport.map_measure,
    ((data.toTransportedNormalGreenData period hPeriod).toTransportedNormalDensityData
      period hPeriod).normalDensity_integrable period hPeriod,
    ((data.toCanonicalNormalGreenData period hPeriod).certificate period hPeriod).2.2.2⟩

end CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreen4D
end JanusFormal

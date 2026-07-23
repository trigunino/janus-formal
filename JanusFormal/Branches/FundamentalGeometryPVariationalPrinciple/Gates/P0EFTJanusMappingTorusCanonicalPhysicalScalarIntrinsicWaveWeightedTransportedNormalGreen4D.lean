import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalHalfCollarTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

/-!
# Intrinsic Green data from corrected weighted normal transport

The affine normal transport becomes a factor-two transport after multiplying
the physical coarea measure by its explicit normal Radon--Nikodym correction.
This constructs the normal Green density, its integrability, and its exact
`-2` half-collar integral.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreen4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalHalfCollarTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Intrinsic-wave Green data using the corrected affine normal transport. -/
structure CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
    (massSquared : Real) where
  intrinsicWave : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod
  tangential_base_integral_zero :
    ∀ field test normal,
      (∫ base,
        (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test (base, normal) +
          (canonicalLatitudeNormalHalfCollarCorrection normal).toReal *
            canonicalPhysicalScalarHalfCollarDivergenceDensity
              period hPeriod massSquared field test
              (canonicalLatitudeWeightedNormalToHalfCollarTransport
                (base, normal)))
        ∂canonicalLatitudeBaseMeasure period) = 0

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData

/-- Corrected pullback of the negative half-collar divergence. -/
def normalDensity
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  -((canonicalLatitudeNormalHalfCollarCorrection parameter.2).toReal *
    canonicalPhysicalScalarHalfCollarDivergenceDensity
      period hPeriod massSquared field test
      (canonicalLatitudeWeightedNormalToHalfCollarTransport parameter))

/-- The explicit cutoff-collar divergence is integrable. -/
theorem halfCollarDivergence_integrable
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Integrable
      (canonicalPhysicalScalarHalfCollarDivergenceDensity
        period hPeriod massSquared field test)
      (canonicalLatitudeCollarMeasure period) := by
  change Integrable
    (canonicalCutBulkDivergenceDensity
      period hPeriod massSquared field test)
    (canonicalLatitudeCollarMeasure period)
  exact canonicalCutBulkDivergenceDensity_integrable
    period hPeriod massSquared field test

/-- Integrability of the corrected normal density. -/
theorem normalDensity_integrable
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Integrable (data.normalDensity period hPeriod field test)
      (canonicalLatitudeCauchyJetProductMeasure period) := by
  unfold normalDensity
  exact (canonicalLatitudeWeightedNormalToHalfCollar_integrable_comp
    period
    (canonicalPhysicalScalarHalfCollarDivergenceDensity
      period hPeriod massSquared field test)
    (data.halfCollarDivergence_integrable period hPeriod field test)).neg

/-- The corrected transport produces the required `-2` half-collar integral. -/
theorem normal_integral_eq_halfCollar
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      data.normalDensity period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 *
        (∫ base, (∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period) := by
  let collarDensity := canonicalPhysicalScalarHalfCollarDivergenceDensity
    period hPeriod massSquared field test
  have hIntegrable :=
    data.halfCollarDivergence_integrable period hPeriod field test
  have hTransport :=
    canonicalLatitudeWeightedNormalToHalfCollar_integral_comp
      period collarDensity hIntegrable
  have hIterated :=
    canonicalLatitudeCollar_integral_eq_iterated
      period collarDensity hIntegrable
  unfold normalDensity
  rw [integral_neg]
  change -(∫ parameter,
      (canonicalLatitudeNormalHalfCollarCorrection parameter.2).toReal *
        collarDensity
          (canonicalLatitudeWeightedNormalToHalfCollarTransport parameter)
      ∂canonicalLatitudeCauchyJetProductMeasure period) = _
  rw [hTransport, hIterated]
  simp only [collarDensity, canonicalPhysicalScalarHalfCollarDivergenceDensity]
  ring

/-- Conversion to the smallest canonical-normal Green package. -/
def toCanonicalNormalGreenData
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared where
  intrinsicWave := data.intrinsicWave
  normalDensity := data.normalDensity period hPeriod
  normalDensity_integrable := data.normalDensity_integrable period hPeriod
  tangential_base_integral_zero := by
    intro field test normal
    simpa [normalDensity, sub_neg_eq_add] using
      data.tangential_base_integral_zero field test normal
  normal_integral_eq_halfCollar :=
    data.normal_integral_eq_halfCollar period hPeriod

/-- Correct dense physical Green core. -/
def greenCore
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
        period hPeriod massSquared) :=
  (data.toCanonicalNormalGreenData period hPeriod).greenCore period hPeriod

/-- Corrected weighted-transport intrinsic Green certificate. -/
theorem certificate
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData
        period hPeriod massSquared) :
    Measure.map canonicalLatitudeWeightedNormalToHalfCollarTransport
        (canonicalLatitudeCorrectedCauchyJetProductMeasure period) =
      (2 : NNReal) • canonicalLatitudeCollarMeasure period ∧
      (∀ field test,
        Integrable (data.normalDensity period hPeriod field test)
          (canonicalLatitudeCauchyJetProductMeasure period)) ∧
      (∀ field test,
        (∫ parameter,
          data.normalDensity period hPeriod field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) =
        -2 *
          (∫ base, (∫ normal in (0 : Real)..1,
            cutoffCollarScalarCurrentDensitizedDivergence
              period hPeriod massSquared field test base normal)
            ∂canonicalLatitudeBaseMeasure period)) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨map_canonicalLatitudeCorrectedCauchyJetProductMeasure period,
    data.normalDensity_integrable period hPeriod,
    data.normal_integral_eq_halfCollar period hPeriod,
    ((data.toCanonicalNormalGreenData period hPeriod).certificate
      period hPeriod).2.2.2⟩

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGreen4D
end JanusFormal

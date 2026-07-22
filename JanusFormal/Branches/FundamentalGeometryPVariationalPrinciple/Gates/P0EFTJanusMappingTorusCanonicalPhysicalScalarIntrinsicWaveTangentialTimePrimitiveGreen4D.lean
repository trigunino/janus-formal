import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialTimePrimitive4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D

/-!
# Intrinsic wave with sphere divergence and periodic time primitive

This is the most local current Green input.  Atlas compatibility is supplied by
an intrinsic global scalar-wave representative.  The tangential remainder is
split into a sphere component and a time derivative.  The time integral is
closed automatically from a periodic primitive; only the sphere integral-zero
identity remains.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreen4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialTimePrimitive4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Sphere2 := Metric.sphere (0 : EuclideanR3) 1

/-- Intrinsic-wave Green data with sphere divergence and a periodic time
primitive. -/
structure CanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreenData
    (massSquared : Real) where
  intrinsicWave : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod
  normalDensity :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod →
        CanonicalLatitudeCauchyJetProductParameter → Real
  normalDensity_integrable : ∀ field test,
    Integrable (normalDensity field test)
      (canonicalLatitudeCauchyJetProductMeasure period)
  sphereDensity :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod → Real →
        CanonicalLatitudeBase → Real
  timeDensity :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod → Real →
        CanonicalLatitudeBase → Real
  sphereDensity_integrable : ∀ field test normal,
    Integrable (sphereDensity field test normal)
      (canonicalLatitudeBaseMeasure period)
  timeDensity_integrable : ∀ field test normal,
    Integrable (timeDensity field test normal)
      (canonicalLatitudeBaseMeasure period)
  tangential_remainder_eq : ∀ field test normal base,
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test (base, normal) -
        normalDensity field test (base, normal) =
      sphereDensity field test normal base +
        timeDensity field test normal base
  sphere_integral_zero : ∀ field test normal time,
    (∫ sphere,
      sphereDensity field test normal (sphere, time)
      ∂(volume : Measure EuclideanR3).toSphere) = 0
  timePrimitive :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod → Real → Sphere2 → Real → Real
  timePrimitive_hasDerivAt : ∀ field test normal sphere time,
    HasDerivAt
      (timePrimitive field test normal sphere)
      (timeDensity field test normal (sphere, time)) time
  timeDensity_continuous : ∀ field test normal sphere,
    Continuous (fun time => timeDensity field test normal (sphere, time))
  timePrimitive_endpoints : ∀ field test normal sphere,
    timePrimitive field test normal sphere (max 0 period) =
      timePrimitive field test normal sphere (min 0 period)
  normal_integral_eq_halfCollar :
    ∀ field test,
      (∫ parameter,
        normalDensity field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 *
        (∫ base, (∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period)

namespace CanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreenData

/-- Conversion to the generic time-primitive cancellation package. -/
def toTangentialTimePrimitiveData
    (data : CanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreenData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerTangentialTimePrimitiveData
      period hPeriod massSquared where
  waveNaturality := data.intrinsicWave.toWaveAtlasNaturality
  normalDensity := data.normalDensity
  normalDensity_integrable := data.normalDensity_integrable
  sphereDensity := data.sphereDensity
  timeDensity := data.timeDensity
  sphereDensity_integrable := data.sphereDensity_integrable
  timeDensity_integrable := data.timeDensity_integrable
  tangential_remainder_eq := data.tangential_remainder_eq
  sphere_integral_zero := data.sphere_integral_zero
  timePrimitive := data.timePrimitive
  timePrimitive_hasDerivAt := data.timePrimitive_hasDerivAt
  timeDensity_continuous := data.timeDensity_continuous
  timePrimitive_endpoints := data.timePrimitive_endpoints
  normal_integral_eq_halfCollar := data.normal_integral_eq_halfCollar

/-- Conversion to the smallest canonical-normal Green package. -/
def toCanonicalNormalGreenData
    (data : CanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreenData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared where
  intrinsicWave := data.intrinsicWave
  normalDensity := data.normalDensity
  normalDensity_integrable := data.normalDensity_integrable
  tangential_base_integral_zero :=
    data.toTangentialTimePrimitiveData.toTangentialFiberCancellationData
      |>.tangential_base_integral_zero
  normal_integral_eq_halfCollar := data.normal_integral_eq_halfCollar

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreenData
      period hPeriod massSquared) :=
  data.toCanonicalNormalGreenData.greenCore

/-- Intrinsic time-primitive Green certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreenData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ field test normal sphere,
        (∫ time,
          data.timeDensity field test normal (sphere, time)
          ∂volume.restrict (canonicalLatitudeTimeInterval period)) = 0) ∧
      (∀ field test normal,
        (∫ base,
          (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
              period hPeriod field test (base, normal) -
            data.normalDensity field test (base, normal))
          ∂canonicalLatitudeBaseMeasure period) = 0) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.intrinsicWave.toWaveAtlasNaturality,
    data.toTangentialTimePrimitiveData.time_integral_zero,
    data.toTangentialTimePrimitiveData.toTangentialFiberCancellationData
      |>.tangential_base_integral_zero,
    data.toCanonicalNormalGreenData.certificate.2.2.2⟩

end CanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTangentialTimePrimitiveGreen4D
end JanusFormal

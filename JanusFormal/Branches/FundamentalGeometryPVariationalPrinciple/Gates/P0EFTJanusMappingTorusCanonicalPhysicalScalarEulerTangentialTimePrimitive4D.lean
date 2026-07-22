import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialFiberCancellation4D

/-!
# Periodic time cancellation by the fundamental theorem of calculus

The time component of a tangential divergence is a derivative along one
fundamental mapping-torus period.  If its primitive has matching endpoint
values, its period integral vanishes by the fundamental theorem of calculus.

This file removes the time-integral-zero field from the tangential Green input.
Only the derivative formula, continuity of the derivative and the endpoint
matching condition remain.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialTimePrimitive4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialFiberCancellation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Sphere2 := Metric.sphere (0 : EuclideanR3) 1

/-- Tangential cancellation data with the time component presented as the
derivative of a periodic primitive. -/
structure CanonicalPhysicalScalarEulerTangentialTimePrimitiveData
    (massSquared : Real) where
  waveNaturality :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod
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

namespace CanonicalPhysicalScalarEulerTangentialTimePrimitiveData

/-- The time derivative integrates to zero over one fundamental period. -/
theorem time_integral_zero
    (data : CanonicalPhysicalScalarEulerTangentialTimePrimitiveData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (normal : Real) (sphere : Sphere2) :
    (∫ time,
      data.timeDensity field test normal (sphere, time)
      ∂volume.restrict (canonicalLatitudeTimeInterval period)) = 0 := by
  have hOrder : min 0 period ≤ max 0 period := min_le_max _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := min 0 period) (b := max 0 period)
    (fun time _ => data.timePrimitive_hasDerivAt
      field test normal sphere time)
    ((data.timeDensity_continuous field test normal sphere)
      |>.intervalIntegrable (min 0 period) (max 0 period))
  rw [intervalIntegral.integral_of_le hOrder] at hFTC
  unfold canonicalLatitudeTimeInterval
  rw [hFTC, data.timePrimitive_endpoints field test normal sphere, sub_self]

/-- Conversion to the sphere/time fiber cancellation package. -/
def toTangentialFiberCancellationData
    (data : CanonicalPhysicalScalarEulerTangentialTimePrimitiveData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerTangentialFiberCancellationData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  normalDensity := data.normalDensity
  normalDensity_integrable := data.normalDensity_integrable
  sphereDensity := data.sphereDensity
  timeDensity := data.timeDensity
  sphereDensity_integrable := data.sphereDensity_integrable
  timeDensity_integrable := data.timeDensity_integrable
  tangential_remainder_eq := data.tangential_remainder_eq
  sphere_integral_zero := data.sphere_integral_zero
  time_integral_zero := data.time_integral_zero
  normal_integral_eq_halfCollar := data.normal_integral_eq_halfCollar

/-- Canonical one-normal-component Green package. -/
def toCanonicalNormalSplitData
    (data : CanonicalPhysicalScalarEulerTangentialTimePrimitiveData
      period hPeriod massSquared) :=
  data.toTangentialFiberCancellationData.toCanonicalNormalSplitData

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarEulerTangentialTimePrimitiveData
      period hPeriod massSquared) :=
  data.toCanonicalNormalSplitData.greenCore

/-- Time-primitive cancellation certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerTangentialTimePrimitiveData
      period hPeriod massSquared) :
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
  ⟨data.time_integral_zero,
    data.toTangentialFiberCancellationData.tangential_base_integral_zero,
    data.toCanonicalNormalSplitData.certificate.2.2.2⟩

end CanonicalPhysicalScalarEulerTangentialTimePrimitiveData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialTimePrimitive4D
end JanusFormal

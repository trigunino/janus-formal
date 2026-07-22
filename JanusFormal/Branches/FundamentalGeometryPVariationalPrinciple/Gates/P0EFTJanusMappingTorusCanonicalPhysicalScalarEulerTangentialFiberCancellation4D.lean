import Mathlib.MeasureTheory.Integral.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalNormalSplit4D

/-!
# Tangential Green cancellation from sphere and time fibers

The canonical boundary base is exactly

`S² × one fundamental time interval`

with product measure.  A tangential divergence can therefore be separated into

* a sphere-divergence density whose sphere integral vanishes for each time;
* a time-divergence density whose one-period integral vanishes for each sphere
  point.

Fubini then gives zero total tangential integral.  This file converts those two
fiberwise identities into the canonical one-normal-component Green package.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialFiberCancellation4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalNormalSplit4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Sphere2 := Metric.sphere (0 : EuclideanR3) 1

private def canonicalLatitudeSphereMeasure : Measure Sphere2 :=
  (volume : Measure EuclideanR3).toSphere

private def canonicalLatitudeTimeMeasure : Measure Real :=
  volume.restrict (canonicalLatitudeTimeInterval period)

/-- Normal Green density together with a sphere/time decomposition of the
induced tangential remainder. -/
structure CanonicalPhysicalScalarEulerTangentialFiberCancellationData
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
      ∂canonicalLatitudeSphereMeasure) = 0
  time_integral_zero : ∀ field test normal sphere,
    (∫ time,
      timeDensity field test normal (sphere, time)
      ∂canonicalLatitudeTimeMeasure period) = 0
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

namespace CanonicalPhysicalScalarEulerTangentialFiberCancellationData

/-- The sphere-divergence component has zero total base integral. -/
theorem sphereDensity_integral_zero
    (data : CanonicalPhysicalScalarEulerTangentialFiberCancellationData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (normal : Real) :
    (∫ base,
      data.sphereDensity field test normal base
      ∂canonicalLatitudeBaseMeasure period) = 0 := by
  have hIntegrable := data.sphereDensity_integrable field test normal
  unfold canonicalLatitudeBaseMeasure at hIntegrable ⊢
  rw [integral_prod_symm _ hIntegrable]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun time =>
    data.sphere_integral_zero field test normal time

/-- The periodic-time-divergence component has zero total base integral. -/
theorem timeDensity_integral_zero
    (data : CanonicalPhysicalScalarEulerTangentialFiberCancellationData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (normal : Real) :
    (∫ base,
      data.timeDensity field test normal base
      ∂canonicalLatitudeBaseMeasure period) = 0 := by
  have hIntegrable := data.timeDensity_integrable field test normal
  unfold canonicalLatitudeBaseMeasure at hIntegrable ⊢
  rw [integral_prod _ hIntegrable]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun sphere =>
    data.time_integral_zero field test normal sphere

/-- The induced tangential remainder has zero base integral at every normal
coordinate. -/
theorem tangential_base_integral_zero
    (data : CanonicalPhysicalScalarEulerTangentialFiberCancellationData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (normal : Real) :
    (∫ base,
      (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test (base, normal) -
        data.normalDensity field test (base, normal))
      ∂canonicalLatitudeBaseMeasure period) = 0 := by
  have hSphere := data.sphereDensity_integrable field test normal
  have hTime := data.timeDensity_integrable field test normal
  calc
    (∫ base,
      (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test (base, normal) -
        data.normalDensity field test (base, normal))
      ∂canonicalLatitudeBaseMeasure period) =
        ∫ base,
          (data.sphereDensity field test normal base +
            data.timeDensity field test normal base)
          ∂canonicalLatitudeBaseMeasure period := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base =>
        data.tangential_remainder_eq field test normal base
    _ =
        (∫ base,
          data.sphereDensity field test normal base
          ∂canonicalLatitudeBaseMeasure period) +
        ∫ base,
          data.timeDensity field test normal base
          ∂canonicalLatitudeBaseMeasure period :=
      integral_add hSphere hTime
    _ = 0 := by
      rw [data.sphereDensity_integral_zero field test normal,
        data.timeDensity_integral_zero field test normal, add_zero]

/-- Conversion to the canonical one-normal-component Green package. -/
def toCanonicalNormalSplitData
    (data : CanonicalPhysicalScalarEulerTangentialFiberCancellationData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  normalDensity := data.normalDensity
  normalDensity_integrable := data.normalDensity_integrable
  tangential_base_integral_zero :=
    data.tangential_base_integral_zero
  normal_integral_eq_halfCollar := data.normal_integral_eq_halfCollar

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarEulerTangentialFiberCancellationData
      period hPeriod massSquared) :=
  data.toCanonicalNormalSplitData.greenCore

/-- Fiber-cancellation Green certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerTangentialFiberCancellationData
      period hPeriod massSquared) :
    (∀ field test normal,
      (∫ base,
        data.sphereDensity field test normal base
        ∂canonicalLatitudeBaseMeasure period) = 0) ∧
      (∀ field test normal,
        (∫ base,
          data.timeDensity field test normal base
          ∂canonicalLatitudeBaseMeasure period) = 0) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.sphereDensity_integral_zero,
    data.timeDensity_integral_zero,
    data.toCanonicalNormalSplitData.certificate.2.2.2⟩

end CanonicalPhysicalScalarEulerTangentialFiberCancellationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerTangentialFiberCancellation4D
end JanusFormal

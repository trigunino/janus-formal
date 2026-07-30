import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalExponentialCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D

/-!
# Spatial conformal Einstein--Hilbert closure

The explicit exponential conformal line realizes the previously computed
Einstein--Hilbert density and action curves.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertClosure4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarWave4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
open P0EFTJanusMappingTorusSpatialConformalExponentialBridge4D
open P0EFTJanusMappingTorusSpatialConformalExponentialCurvature4D
open P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The genuine Lorentz metric `g_t = exp (2 t u) g₀`. -/
def spatialConformalExponentialMetric
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) :
    SmoothGeneralLorentzMetric period hPeriod :=
  conformalSmoothGeneralLorentzMetric period hPeriod
    (spatialConformalExponentialScale
      period hPeriod direction parameter)
    (spatialConformalExponentialScale_pos
      period hPeriod direction parameter)

theorem globalMetricVolumeRatio_spatialConformalExponentialMetric
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod
        (spatialConformalExponentialMetric
          period hPeriod direction parameter) point =
      Real.exp (4 * parameter * direction point) := by
  unfold spatialConformalExponentialMetric
  rw [globalMetricVolumeRatio_conformal]
  simp only [spatialConformalExponentialScale_apply]
  calc
    Real.exp (2 * parameter * direction point) ^ 2 =
        Real.exp
          ((2 * parameter * direction point) +
            (2 * parameter * direction point)) := by
      rw [pow_two, ← Real.exp_add]
    _ = Real.exp (4 * parameter * direction point) := by
      congr 1
      ring

theorem weightedFrameFreeEinsteinHilbertDensity_spatialConformalExponentialMetric
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod
        (spatialConformalExponentialMetric
          period hPeriod direction parameter) point *
      frameFreeEinsteinHilbertDensity period hPeriod
        (spatialConformalExponentialMetric
          period hPeriod direction parameter) couplings point =
      spatialConformalEHDensityCurve
        period hPeriod couplings direction parameter point := by
  rw [globalMetricVolumeRatio_spatialConformalExponentialMetric]
  unfold spatialConformalExponentialMetric
  unfold frameFreeEinsteinHilbertDensity
  simp only [globalSmoothScalarCurvature_apply]
  rw [globalScalarCurvature_spatialConformalExponentialScale]
  unfold spatialConformalEHDensityCurve
  change
    Real.exp (4 * parameter * direction point) *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (Real.exp (-2 * parameter * direction point) *
              (globalScalarCurvature period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod) point -
                6 * parameter *
                  canonicalGlobalSmoothScalarWave
                    period hPeriod direction point -
                6 * parameter ^ 2 *
                  canonicalGlobalScalarGradientPairing
                    period hPeriod direction direction point) -
            2 * couplings.cosmologicalConstant)) =
      (1 / (2 * couplings.gravitationalCoupling)) *
        (Real.exp (2 * parameter * direction point) *
            (globalScalarCurvature period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod) point -
              6 * parameter *
                canonicalGlobalSmoothScalarWave
                  period hPeriod direction point -
              6 * parameter ^ 2 *
                canonicalGlobalScalarGradientPairing
                  period hPeriod direction direction point) -
          2 * couplings.cosmologicalConstant *
            Real.exp (4 * parameter * direction point))
  have hExponential :
      Real.exp (4 * parameter * direction point) *
          Real.exp (-2 * parameter * direction point) =
        Real.exp (2 * parameter * direction point) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hExponential]
  ring

theorem generalLorentzFrameFreeEinsteinHilbertAction_spatialConformalExponentialMetric
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) :
    generalLorentzFrameFreeEinsteinHilbertAction period hPeriod
        (spatialConformalExponentialMetric
          period hPeriod direction parameter) couplings =
      spatialConformalEHActionCurve
        period hPeriod couplings direction parameter := by
  rw [generalLorentzFrameFreeEinsteinHilbertAction_eq_reference]
  unfold spatialConformalEHActionCurve
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    weightedFrameFreeEinsteinHilbertDensity_spatialConformalExponentialMetric
      period hPeriod couplings direction parameter point

theorem generalLorentzFrameFreeEinsteinHilbertAction_spatialConformalExponentialMetric_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) :
    HasDerivAt
      (fun varied =>
        generalLorentzFrameFreeEinsteinHilbertAction period hPeriod
          (spatialConformalExponentialMetric
            period hPeriod direction varied) couplings)
      (spatialConformalEHActionFirstDerivative
        period hPeriod couplings direction parameter)
      parameter := by
  simpa only [
    generalLorentzFrameFreeEinsteinHilbertAction_spatialConformalExponentialMetric]
    using spatialConformalEHActionCurve_hasDerivAt
      period hPeriod couplings direction parameter

theorem generalLorentzFrameFreeEinsteinHilbertAction_spatialConformalExponentialMetric_hasSecondVariationAt_zero
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod) :
    HasDerivAt
        (fun parameter =>
          generalLorentzFrameFreeEinsteinHilbertAction period hPeriod
            (spatialConformalExponentialMetric
              period hPeriod direction parameter) couplings)
        (spatialConformalEHActionFirstDerivative
          period hPeriod couplings direction 0) 0 ∧
      HasDerivAt
        (spatialConformalEHActionFirstDerivative
          period hPeriod couplings direction)
        (spatialConformalEHHessian
          period hPeriod couplings direction direction) 0 := by
  exact
    ⟨generalLorentzFrameFreeEinsteinHilbertAction_spatialConformalExponentialMetric_hasDerivAt
        period hPeriod couplings direction 0,
      spatialConformalEHActionFirstDerivative_hasSecondDerivAt_zero
        period hPeriod couplings direction⟩

end

end P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertClosure4D
end JanusFormal

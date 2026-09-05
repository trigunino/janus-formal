import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-!
# Canonical metric-volume divergence and global Stokes theorem

The ten canonical volume-preserving flows provide a global divergence for the
fixed reference volume.  Densitizing a tangent current by the intrinsic
Lorentz-volume ratio and dividing back defines the corresponding metric-volume
divergence.  Its strong and weak Stokes identities are unconditional on the
compact boundaryless quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Tangent current densitized by the intrinsic metric-volume ratio. -/
def canonicalMetricVolumeCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    SmoothTangentField period hPeriod :=
  smoothScalarSMulTangentField period hPeriod
    (globalSmoothMetricVolumeRatio period hPeriod metric.metric) vector

@[simp]
theorem canonicalMetricVolumeCurrent_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalMetricVolumeCurrent period hPeriod metric vector point =
      globalMetricVolumeRatio period hPeriod metric.metric point •
        vector point :=
  rfl

/-- Global divergence associated with the intrinsic Lorentz volume. -/
def canonicalMetricVolumeDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    canonicalTenFlowDivergence period hPeriod metric
        (canonicalMetricVolumeCurrent period hPeriod metric vector) point /
      globalMetricVolumeRatio period hPeriod metric.metric point
  contMDiff_toFun :=
    (canonicalTenFlowDivergence period hPeriod metric
      (canonicalMetricVolumeCurrent period hPeriod metric vector)
      ).contMDiff_toFun.div₀
      (globalSmoothMetricVolumeRatio period hPeriod metric.metric
        ).contMDiff_toFun
      (fun point => ne_of_gt
        (globalMetricVolumeRatio_pos period hPeriod metric.metric point))

/-- Densitization turns the metric-volume divergence back into the canonical
reference-volume divergence. -/
theorem globalMetricVolumeRatio_mul_canonicalMetricVolumeDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod metric.metric point *
        canonicalMetricVolumeDivergence period hPeriod metric vector point =
      canonicalTenFlowDivergence period hPeriod metric
        (canonicalMetricVolumeCurrent period hPeriod metric vector) point := by
  change globalMetricVolumeRatio period hPeriod metric.metric point *
      (canonicalTenFlowDivergence period hPeriod metric
          (canonicalMetricVolumeCurrent period hPeriod metric vector) point /
        globalMetricVolumeRatio period hPeriod metric.metric point) = _
  field_simp [ne_of_gt
    (globalMetricVolumeRatio_pos period hPeriod metric.metric point)]

theorem canonicalMetricVolumeDivergence_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    Integrable (canonicalMetricVolumeDivergence period hPeriod metric vector)
      (generalLorentzVolumeMeasure period hPeriod metric.metric) := by
  letI : IsFiniteMeasure
      (generalLorentzVolumeMeasure period hPeriod metric.metric) :=
    generalLorentzVolumeMeasure_isFinite period hPeriod metric.metric
  exact (canonicalMetricVolumeDivergence period hPeriod metric vector
    ).contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Boundaryless Stokes theorem for the intrinsic metric-volume divergence. -/
theorem canonicalMetricVolumeDivergence_integral_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    (∫ point, canonicalMetricVolumeDivergence period hPeriod metric vector point
      ∂generalLorentzVolumeMeasure period hPeriod metric.metric) = 0 := by
  rw [integral_generalLorentzVolumeMeasure_eq_reference]
  calc
    (∫ point,
        globalMetricVolumeRatio period hPeriod metric.metric point *
          canonicalMetricVolumeDivergence period hPeriod metric vector point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        ∫ point,
          canonicalTenFlowDivergence period hPeriod metric
            (canonicalMetricVolumeCurrent period hPeriod metric vector) point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point =>
        globalMetricVolumeRatio_mul_canonicalMetricVolumeDivergence
          period hPeriod metric vector point
    _ = 0 := canonicalTenFlowDivergence_integral_eq_zero period hPeriod metric
      (canonicalMetricVolumeCurrent period hPeriod metric vector)

/-- Weak metric-volume Stokes identity for every smooth scalar test. -/
theorem canonicalMetricVolumeDivergence_weak_stokes
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real) :
    (∫ point,
        test point *
          canonicalMetricVolumeDivergence period hPeriod metric vector point
      ∂generalLorentzVolumeMeasure period hPeriod metric.metric) =
      -∫ point,
        mvfderiv coverModelWithCorners test.toFun point (vector point)
      ∂generalLorentzVolumeMeasure period hPeriod metric.metric := by
  rw [integral_generalLorentzVolumeMeasure_eq_reference,
    integral_generalLorentzVolumeMeasure_eq_reference]
  calc
    (∫ point,
        globalMetricVolumeRatio period hPeriod metric.metric point *
          (test point *
            canonicalMetricVolumeDivergence period hPeriod metric vector point)
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        ∫ point,
          test point *
            canonicalTenFlowDivergence period hPeriod metric
              (canonicalMetricVolumeCurrent period hPeriod metric vector) point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      filter_upwards [] with point
      rw [← globalMetricVolumeRatio_mul_canonicalMetricVolumeDivergence
        period hPeriod metric vector point]
      ring
    _ = -∫ point,
        mvfderiv coverModelWithCorners test.toFun point
          (canonicalMetricVolumeCurrent period hPeriod metric vector point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod :=
      canonicalTenFlowDivergence_weak_stokes period hPeriod metric
        (canonicalMetricVolumeCurrent period hPeriod metric vector) test
    _ = -∫ point,
        globalMetricVolumeRatio period hPeriod metric.metric point *
          mvfderiv coverModelWithCorners test.toFun point (vector point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with point
      change mvfderiv coverModelWithCorners test.toFun point
          (globalMetricVolumeRatio period hPeriod metric.metric point •
            vector point) = _
      rw [map_smul]
      rfl

/-- Gate marker: intrinsic metric-volume divergence has both strong and weak
global Stokes identities, with no boundary or integrability assumptions left
as external contracts. -/
theorem canonical_metric_volume_divergence_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    Integrable (canonicalMetricVolumeDivergence period hPeriod metric vector)
        (generalLorentzVolumeMeasure period hPeriod metric.metric) ∧
      (∫ point,
        canonicalMetricVolumeDivergence period hPeriod metric vector point
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric) = 0 ∧
      ∀ test : SmoothQuotientField period hPeriod Real,
        (∫ point,
            test point *
              canonicalMetricVolumeDivergence period hPeriod metric vector point
          ∂generalLorentzVolumeMeasure period hPeriod metric.metric) =
          -∫ point,
            mvfderiv coverModelWithCorners test.toFun point (vector point)
          ∂generalLorentzVolumeMeasure period hPeriod metric.metric := by
  exact ⟨canonicalMetricVolumeDivergence_integrable period hPeriod metric vector,
    canonicalMetricVolumeDivergence_integral_eq_zero period hPeriod metric vector,
    canonicalMetricVolumeDivergence_weak_stokes period hPeriod metric vector⟩

end
end P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
end JanusFormal

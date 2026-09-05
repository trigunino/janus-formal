import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D

/-!
# Stored-frame Einstein--Hilbert action as a weighted frame-free action

The legacy regular metric stores the determinant density of an arbitrary
global frame.  Against the canonical reference measure this inserts one
explicit scalar weight into the frame-free metric-volume action.  This file
isolates that weight and the exact compatibility condition under which the
legacy and frame-free physical actions coincide.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev regularEinsteinHilbertMetric
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
    period hPeriod metric

/-- Scalar converting the intrinsic metric volume into the stored-frame
volume scalar used by the legacy action. -/
def regularFrameEinsteinHilbertActionWeight
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    metric.volume point /
      globalMetricVolumeRatio period hPeriod metric.metric point
  contMDiff_toFun :=
    metric.volume.contMDiff_toFun.div₀
      (globalSmoothMetricVolumeRatio period hPeriod metric.metric
        ).contMDiff_toFun
      (fun point =>
        ne_of_gt
          (globalMetricVolumeRatio_pos period hPeriod metric.metric point))

@[simp]
theorem regularFrameEinsteinHilbertActionWeight_mul_volumeRatio
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod metric.metric point *
        regularFrameEinsteinHilbertActionWeight period hPeriod metric point =
      metric.volume point := by
  unfold regularFrameEinsteinHilbertActionWeight
  field_simp [ne_of_gt
    (globalMetricVolumeRatio_pos period hPeriod metric.metric point)]

/-- The frame-free Einstein--Hilbert action with the exact scalar weight
selected by the stored regular frame. -/
def regularFrameWeightedFrameFreeEinsteinHilbertAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) : Real :=
  ∫ point,
    regularFrameEinsteinHilbertActionWeight period hPeriod metric point *
      frameFreeEinsteinHilbertDensity period hPeriod metric.metric couplings
        point
    ∂generalLorentzVolumeMeasure period hPeriod metric.metric

/-- The legacy stored-frame EH action against canonical volume is exactly
the globally weighted frame-free action. -/
theorem regularFrameWeightedFrameFreeEinsteinHilbertAction_eq_intrinsic
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    regularFrameWeightedFrameFreeEinsteinHilbertAction period hPeriod metric
        couplings =
      intrinsicEinsteinHilbertAction period hPeriod couplings
        (regularEinsteinHilbertMetric period hPeriod metric)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold regularFrameWeightedFrameFreeEinsteinHilbertAction
    intrinsicEinsteinHilbertAction
  rw [integral_generalLorentzVolumeMeasure_eq_reference]
  apply integral_congr_ae
  filter_upwards [] with point
  calc
    globalMetricVolumeRatio period hPeriod metric.metric point *
          (regularFrameEinsteinHilbertActionWeight period hPeriod metric point *
            frameFreeEinsteinHilbertDensity period hPeriod metric.metric
              couplings point) =
        (globalMetricVolumeRatio period hPeriod metric.metric point *
            regularFrameEinsteinHilbertActionWeight period hPeriod metric
              point) *
          frameFreeEinsteinHilbertDensity period hPeriod metric.metric
            couplings point := by ring
    _ = metric.volume point *
          frameFreeEinsteinHilbertDensity period hPeriod metric.metric
            couplings point := by
      rw [regularFrameEinsteinHilbertActionWeight_mul_volumeRatio]
    _ = regularEinsteinHilbertDensityField period hPeriod couplings
          (regularEinsteinHilbertMetric period hPeriod metric) point := rfl

/-- Canonical-volume gauge: the stored scalar is the intrinsic metric-volume
ratio relative to the fixed canonical action measure. -/
def RegularGeneralMetricInCanonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod) : Prop :=
  metric.volume = globalSmoothMetricVolumeRatio period hPeriod metric.metric

theorem regularFrameEinsteinHilbertActionWeight_eq_one_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameEinsteinHilbertActionWeight period hPeriod metric point = 1 := by
  have hPoint := congrArg
    (fun field : SmoothScalarField period hPeriod => field point) hGauge
  change metric.volume point =
    globalMetricVolumeRatio period hPeriod metric.metric point at hPoint
  change metric.volume point /
      globalMetricVolumeRatio period hPeriod metric.metric point = 1
  rw [hPoint, div_self (ne_of_gt
    (globalMetricVolumeRatio_pos period hPeriod metric.metric point))]

/-- In canonical-volume gauge the legacy action is exactly the physical
frame-free metric-volume Einstein--Hilbert action. -/
theorem intrinsicEinsteinHilbertAction_eq_frameFree_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric) :
    intrinsicEinsteinHilbertAction period hPeriod couplings
        (regularEinsteinHilbertMetric period hPeriod metric)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      generalLorentzFrameFreeEinsteinHilbertAction period hPeriod metric.metric
        couplings := by
  rw [← regularFrameWeightedFrameFreeEinsteinHilbertAction_eq_intrinsic
    period hPeriod metric couplings]
  unfold regularFrameWeightedFrameFreeEinsteinHilbertAction
    generalLorentzFrameFreeEinsteinHilbertAction
    frameFreeEinsteinHilbertAction
  apply integral_congr_ae
  filter_upwards [] with point
  rw [regularFrameEinsteinHilbertActionWeight_eq_one_of_canonicalVolumeGauge
    period hPeriod metric hGauge point, one_mul]

/-- Gate marker: the stored-frame weight is explicit, and canonical-volume
gauge removes it exactly. -/
theorem regular_frame_einstein_hilbert_frame_free_action_measure_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    regularFrameWeightedFrameFreeEinsteinHilbertAction period hPeriod metric
        couplings =
      intrinsicEinsteinHilbertAction period hPeriod couplings
        (regularEinsteinHilbertMetric period hPeriod metric)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      ∀ _hGauge : RegularGeneralMetricInCanonicalVolumeGauge
          period hPeriod metric,
        intrinsicEinsteinHilbertAction period hPeriod couplings
            (regularEinsteinHilbertMetric period hPeriod metric)
            (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
          generalLorentzFrameFreeEinsteinHilbertAction period hPeriod
            metric.metric couplings := by
  exact ⟨
    regularFrameWeightedFrameFreeEinsteinHilbertAction_eq_intrinsic
      period hPeriod metric couplings,
    fun hGauge =>
      intrinsicEinsteinHilbertAction_eq_frameFree_of_canonicalVolumeGauge
        period hPeriod metric couplings hGauge⟩

end
end P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
end JanusFormal

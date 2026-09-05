import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D

/-! # Stored-frame Maxwell action as a weighted frame-free action -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellFrameFreeActionMeasureBridge4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Global scalar converting the metric volume measure into the volume scalar
stored with the chosen regular frame. -/
def regularFrameMaxwellActionWeight
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
theorem regularFrameMaxwellActionWeight_mul_volumeRatio
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod metric.metric point *
        regularFrameMaxwellActionWeight period hPeriod metric point =
      metric.volume point := by
  unfold regularFrameMaxwellActionWeight
  field_simp [ne_of_gt
    (globalMetricVolumeRatio_pos period hPeriod metric.metric point)]

/-- The frame-free Maxwell action with the exact scalar weight selected by
the stored regular frame. -/
def regularFrameWeightedFrameFreeMaxwellAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) : Real :=
  ∫ point,
    regularFrameMaxwellActionWeight period hPeriod metric point *
      frameFreeMaxwellDensity period hPeriod metric.metric potential point
    ∂generalLorentzVolumeMeasure period hPeriod metric.metric

/-- Candidate A's stored-frame Maxwell action against canonical volume is
exactly a globally weighted frame-free Maxwell action. -/
theorem regularFrameWeightedFrameFreeMaxwellAction_eq_intrinsic
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameWeightedFrameFreeMaxwellAction period hPeriod metric
        potential =
      intrinsicMaxwellAction period hPeriod metric
        (globalSmoothMaxwellPairing period hPeriod metric.metric potential
          potential)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold regularFrameWeightedFrameFreeMaxwellAction intrinsicMaxwellAction
  rw [integral_generalLorentzVolumeMeasure_eq_reference]
  apply integral_congr_ae
  filter_upwards [] with point
  calc
    globalMetricVolumeRatio period hPeriod metric.metric point *
          (regularFrameMaxwellActionWeight period hPeriod metric point *
            frameFreeMaxwellDensity period hPeriod metric.metric potential
              point) =
        (globalMetricVolumeRatio period hPeriod metric.metric point *
            regularFrameMaxwellActionWeight period hPeriod metric point) *
          frameFreeMaxwellDensity period hPeriod metric.metric potential
            point := by ring
    _ = metric.volume point *
          frameFreeMaxwellDensity period hPeriod metric.metric potential
            point := by
      rw [regularFrameMaxwellActionWeight_mul_volumeRatio]
    _ = metric.volume point *
          (-(1 / 4 : Real) *
            globalSmoothMaxwellPairing period hPeriod metric.metric potential
              potential point) := rfl

/-- Gate marker: the frame dependence is one explicit global scalar coupling,
not an unproved constant Jacobian. -/
theorem regular_frame_maxwell_frame_free_action_measure_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameWeightedFrameFreeMaxwellAction period hPeriod metric
        potential =
      intrinsicMaxwellAction period hPeriod metric
        (globalSmoothMaxwellPairing period hPeriod metric.metric potential
          potential)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  regularFrameWeightedFrameFreeMaxwellAction_eq_intrinsic period hPeriod
    metric potential

end

end P0EFTJanusProgramPRegularFrameMaxwellFrameFreeActionMeasureBridge4D
end JanusFormal

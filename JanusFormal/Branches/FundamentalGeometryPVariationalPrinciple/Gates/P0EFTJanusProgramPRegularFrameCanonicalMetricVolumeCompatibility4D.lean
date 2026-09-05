import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertWeightedPalatiniResidual4D

/-!
# Canonical metric-volume compatibility from the ten finite obstructions

In canonical-volume gauge, differentiating the global metric-volume ratio
contributes the metric half-trace.  The ten-generator identification supplies
the remaining anholonomy trace.  Their sum is the Levi--Civita trace, so the
four Palatini compatibility residuals and the full smooth Palatini defect
vanish.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMetricVolumeCompatibility4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceCalculus4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D
open P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D
open P0EFTJanusProgramPRegularFrameMetricVolumeDerivative4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertWeightedPalatiniResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- On every regular-frame vector, metric-volume divergence is the sum of
the metric half-trace and the recollé canonical anholonomy trace. -/
theorem canonicalMetricVolumeDivergence_frame_eq_halfTrace_add_canonical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0)
    (vector : Index4) :
    canonicalMetricVolumeDivergence period hPeriod metric
        (metric.frame vector) =
      regularFrameMetricHalfTraceDerivative period hPeriod metric vector +
        regularFrameCanonicalDivergence period hPeriod metric vector := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  let ratio := globalSmoothMetricVolumeRatio period hPeriod metric.metric
  have hRatioNe : ratio point ≠ 0 :=
    ne_of_gt (globalMetricVolumeRatio_pos period hPeriod metric.metric point)
  have hCanonicalField :=
    regularFrameCanonicalDivergence_eq_canonical_of_generator_zero
      period hPeriod metric hGenerators vector
  have hCanonical := congrArg
    (fun field : SmoothScalarField period hPeriod => field point)
    hCanonicalField
  change regularFrameCanonicalDivergence period hPeriod metric vector point =
    canonicalTenFlowDivergence period hPeriod metric (metric.frame vector)
      point at hCanonical
  have hRatioDerivative :=
    regularFrameMetricVolume_frameDerivative period hPeriod metric point vector
  rw [hGauge] at hRatioDerivative
  rw [frameDerivative_eq_mfderiv] at hRatioDerivative
  change mvfderiv coverModelWithCorners ratio.toFun point
      (metric.frame vector point) =
    ratio point *
      regularFrameMetricHalfTraceDerivative period hPeriod metric vector point
        at hRatioDerivative
  change
    canonicalTenFlowDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod ratio
          (metric.frame vector)) point /
        ratio point =
      regularFrameMetricHalfTraceDerivative period hPeriod metric vector point +
        regularFrameCanonicalDivergence period hPeriod metric vector point
  rw [canonicalTenFlowDivergence_smul_apply]
  rw [← hCanonical, hRatioDerivative]
  field_simp [hRatioNe]
  ring

/-- The four frame compatibility residuals vanish once the ten finite
canonical-generator residuals vanish. -/
theorem regularFrameCanonicalDivergenceCompatibilityResidual_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0)
    (vector : Index4) :
    regularFrameCanonicalDivergenceCompatibilityResidual period hPeriod
      metric vector = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hTrace := congrArg
    (fun field : SmoothScalarField period hPeriod => field point)
    (regularFrameLeviCivitaTrace_eq_halfTrace_add_anholonomy
      period hPeriod metric vector)
  change regularFrameLeviCivitaTrace period hPeriod metric vector point =
    regularFrameMetricHalfTraceDerivative period hPeriod metric vector point +
      regularFrameAnholonomyTrace period hPeriod metric vector point at hTrace
  have hDivergence := congrArg
    (fun field : SmoothScalarField period hPeriod => field point)
    (canonicalMetricVolumeDivergence_frame_eq_halfTrace_add_canonical
      period hPeriod metric hGauge hGenerators vector)
  change canonicalMetricVolumeDivergence period hPeriod metric
      (metric.frame vector) point =
    regularFrameMetricHalfTraceDerivative period hPeriod metric vector point +
      regularFrameAnholonomyTrace period hPeriod metric vector point
        at hDivergence
  change regularFrameLeviCivitaTrace period hPeriod metric vector point -
      canonicalMetricVolumeDivergence period hPeriod metric
        (metric.frame vector) point = 0
  rw [hTrace, hDivergence]
  ring

/-- The smooth Palatini covariant divergence is therefore the canonical
metric-volume divergence for every smooth metric variation. -/
theorem regularFrameSmoothPalatiniCovariantDivergence_eq_canonical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0) :
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor =
      canonicalMetricVolumeDivergence period hPeriod metric
        (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric
          tensor) :=
  regularFrameSmoothPalatiniCovariantDivergence_eq_canonical_of_frameCompatible
    period hPeriod metric tensor
      (regularFrameCanonicalDivergenceCompatibilityResidual_eq_zero
        period hPeriod metric hGauge hGenerators)

/-- The full pointwise Palatini defect used by the weighted EH derivative is
identically zero under the same finite geometric hypotheses. -/
theorem regularGeneralMetricC2PalatiniCanonicalDivergenceDefect_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0) :
    regularGeneralMetricC2PalatiniCanonicalDivergenceDefect period hPeriod
      metric tensor = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hPalatini := congrArg
    (fun field : SmoothScalarField period hPeriod => field point)
    (regularFrameSmoothPalatiniCovariantDivergence_eq_canonical
      period hPeriod metric tensor hGauge hGenerators)
  change regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
      tensor point =
    canonicalMetricVolumeDivergence period hPeriod metric
      (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor)
      point at hPalatini
  change regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
      tensor point -
    canonicalMetricVolumeDivergence period hPeriod metric
      (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor)
      point = 0
  rw [hPalatini]
  ring

/-- The Einstein--Hilbert derivative now has its pure invariant bulk form;
the former unrestricted Palatini defect has been reduced to ten named scalar
equations. -/
theorem regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantBulk
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point,
        -(1 / (2 * couplings.gravitationalCoupling)) *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
              couplings.cosmologicalConstant) tensor point
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric :=
  regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantBulk_of_canonicalVolumeGauge
    period hPeriod metric couplings tensor hGauge
      (regularGeneralMetricC2PalatiniCanonicalDivergenceDefect_eq_zero
        period hPeriod metric tensor hGauge hGenerators)

/-- Gate marker: metric-volume compatibility and the smooth EH bulk equation
are reduced to the explicit ten-generator geometric obligation. -/
theorem regular_frame_canonical_metric_volume_compatibility_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0) :
    ∀ vector : Index4,
      regularFrameCanonicalDivergenceCompatibilityResidual period hPeriod
        metric vector = 0 :=
  regularFrameCanonicalDivergenceCompatibilityResidual_eq_zero
    period hPeriod metric hGauge hGenerators

end
end P0EFTJanusProgramPRegularFrameCanonicalMetricVolumeCompatibility4D
end JanusFormal

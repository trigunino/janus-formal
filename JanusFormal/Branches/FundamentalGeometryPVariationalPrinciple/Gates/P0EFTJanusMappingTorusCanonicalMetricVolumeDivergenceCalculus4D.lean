import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D

/-! # Linear and Leibniz calculus for canonical metric-volume divergence -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceCalculus4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem canonicalMetricVolumeCurrent_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    canonicalMetricVolumeCurrent period hPeriod metric 0 = 0 := by
  ext point
  simp [canonicalMetricVolumeCurrent_apply]

theorem canonicalMetricVolumeCurrent_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothTangentField period hPeriod) :
    canonicalMetricVolumeCurrent period hPeriod metric (first + second) =
      canonicalMetricVolumeCurrent period hPeriod metric first +
        canonicalMetricVolumeCurrent period hPeriod metric second := by
  ext point
  simp [canonicalMetricVolumeCurrent_apply, smul_add]

theorem canonicalMetricVolumeCurrent_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod) :
    canonicalMetricVolumeCurrent period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) =
      smoothScalarSMulTangentField period hPeriod scalar
        (canonicalMetricVolumeCurrent period hPeriod metric vector) := by
  ext point
  change
    globalMetricVolumeRatio period hPeriod metric.metric point •
        (scalar point • vector point) =
      scalar point •
        (globalMetricVolumeRatio period hPeriod metric.metric point •
          vector point)
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem canonicalMetricVolumeDivergence_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    canonicalMetricVolumeDivergence period hPeriod metric 0 = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    canonicalTenFlowDivergence period hPeriod metric
        (canonicalMetricVolumeCurrent period hPeriod metric 0) point /
      globalMetricVolumeRatio period hPeriod metric.metric point = 0
  rw [canonicalMetricVolumeCurrent_zero period hPeriod metric,
    canonicalTenFlowDivergence_zero]
  change (0 : Real) /
      globalMetricVolumeRatio period hPeriod metric.metric point = 0
  simp

theorem canonicalMetricVolumeDivergence_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothTangentField period hPeriod) :
    canonicalMetricVolumeDivergence period hPeriod metric (first + second) =
      canonicalMetricVolumeDivergence period hPeriod metric first +
        canonicalMetricVolumeDivergence period hPeriod metric second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    canonicalTenFlowDivergence period hPeriod metric
        (canonicalMetricVolumeCurrent period hPeriod metric (first + second))
          point /
        globalMetricVolumeRatio period hPeriod metric.metric point =
      canonicalTenFlowDivergence period hPeriod metric
          (canonicalMetricVolumeCurrent period hPeriod metric first) point /
          globalMetricVolumeRatio period hPeriod metric.metric point +
        canonicalTenFlowDivergence period hPeriod metric
          (canonicalMetricVolumeCurrent period hPeriod metric second) point /
          globalMetricVolumeRatio period hPeriod metric.metric point
  rw [canonicalMetricVolumeCurrent_add period hPeriod metric,
    canonicalTenFlowDivergence_add]
  change (_ + _) / _ = _ / _ + _ / _
  ring

/-- Metric-volume divergence as an additive homomorphism. -/
def canonicalMetricVolumeDivergenceAddMonoidHom
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothTangentField period hPeriod →+
      SmoothQuotientField period hPeriod Real where
  toFun := canonicalMetricVolumeDivergence period hPeriod metric
  map_zero' := canonicalMetricVolumeDivergence_zero period hPeriod metric
  map_add' := canonicalMetricVolumeDivergence_add period hPeriod metric

theorem canonicalMetricVolumeDivergence_finset_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {ι : Type*} (indices : Finset ι)
    (vectors : ι → SmoothTangentField period hPeriod) :
    canonicalMetricVolumeDivergence period hPeriod metric
        (∑ index ∈ indices, vectors index) =
      ∑ index ∈ indices,
        canonicalMetricVolumeDivergence period hPeriod metric
          (vectors index) := by
  exact map_sum (canonicalMetricVolumeDivergenceAddMonoidHom
    period hPeriod metric) (fun index => vectors index) indices

/-- Exact Leibniz rule for the metric-volume divergence. -/
theorem canonicalMetricVolumeDivergence_smul_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalMetricVolumeDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) point =
      scalar point *
          canonicalMetricVolumeDivergence period hPeriod metric vector point +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point) := by
  have hRatioNe :
      globalMetricVolumeRatio period hPeriod metric.metric point ≠ 0 :=
    ne_of_gt (globalMetricVolumeRatio_pos period hPeriod metric.metric point)
  change
    canonicalTenFlowDivergence period hPeriod metric
        (canonicalMetricVolumeCurrent period hPeriod metric
          (smoothScalarSMulTangentField period hPeriod scalar vector)) point /
        globalMetricVolumeRatio period hPeriod metric.metric point =
      scalar point *
          (canonicalTenFlowDivergence period hPeriod metric
              (canonicalMetricVolumeCurrent period hPeriod metric vector) point /
            globalMetricVolumeRatio period hPeriod metric.metric point) +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point)
  rw [canonicalMetricVolumeCurrent_smul period hPeriod metric scalar vector,
    canonicalTenFlowDivergence_smul_apply]
  change
    (scalar point *
          canonicalTenFlowDivergence period hPeriod metric
            (canonicalMetricVolumeCurrent period hPeriod metric vector) point +
        mvfderiv coverModelWithCorners scalar.toFun point
          (globalMetricVolumeRatio period hPeriod metric.metric point •
            vector point)) /
        globalMetricVolumeRatio period hPeriod metric.metric point = _
  rw [map_smul]
  change
    (scalar point * _ +
        globalMetricVolumeRatio period hPeriod metric.metric point *
          mvfderiv coverModelWithCorners scalar.toFun point (vector point)) /
      globalMetricVolumeRatio period hPeriod metric.metric point = _
  field_simp [hRatioNe]

/-- Gate marker: canonical metric-volume divergence is additive and obeys
the pointwise product rule used by frame decompositions. -/
theorem canonical_metric_volume_divergence_calculus_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalMetricVolumeDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) point =
      scalar point *
          canonicalMetricVolumeDivergence period hPeriod metric vector point +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point) :=
  canonicalMetricVolumeDivergence_smul_apply period hPeriod metric scalar
    vector point

end
end P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceCalculus4D
end JanusFormal

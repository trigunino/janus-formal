import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothInverseMusical4D

/-!
# Metric volume-density naturality on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkMetricVolumeDensityNaturality4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

/-- Gram matrix of a cut-bulk metric on an ordered tangent four-frame. -/
def cutBulkMetricGramMatrix
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (frame : Fin 4 → CutBulkTangentFiber period hPeriod point) :
    Matrix (Fin 4) (Fin 4) Real :=
  fun i j => metric.tensor.tensor point (frame i) (frame j)

/-- Absolute metric-density evaluation on a cut-bulk tangent frame. -/
def cutBulkMetricVolumeDensity
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (frame : Fin 4 → CutBulkTangentFiber period hPeriod point) : Real :=
  Real.sqrt |(cutBulkMetricGramMatrix period hPeriod metric point frame).det|

/-- Pullback of an ambient frame by the inverse certified derivative. -/
def cutBulkAmbientFramePullback
    (point : PositiveHemisphereCutBulk period hPeriod)
    (frame : Fin 4 → AmbientTangentFiber period hPeriod point) :
    Fin 4 → CutBulkTangentFiber period hPeriod point :=
  fun index =>
    (cutBulkToAmbientDerivativeEquiv period hPeriod point).symm (frame index)

theorem cutBulkMetricGramMatrix_ambientPullback
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (frame : Fin 4 → AmbientTangentFiber period hPeriod point) :
    cutBulkMetricGramMatrix period hPeriod
        (cutBulkAmbientSmoothGeneralLorentzMetricPullback period hPeriod metric)
        point (cutBulkAmbientFramePullback period hPeriod point frame) =
      metricGramMatrix period hPeriod metric
        (cutBulkToAmbient period hPeriod point) frame := by
  ext first second
  change cutBulkAmbientTensorPullback period hPeriod
      metric.tensor.tensor.toTensorField point
      ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm (frame first))
      ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm (frame second)) =
    metric.tensor.tensor (cutBulkToAmbient period hPeriod point)
      (frame first) (frame second)
  rw [cutBulkAmbientTensorPullback_apply,
    ← DFunLike.congr_fun
      (cutBulkToAmbientDerivativeEquiv_coe period hPeriod point)
      ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm (frame first)),
    ← DFunLike.congr_fun
      (cutBulkToAmbientDerivativeEquiv_coe period hPeriod point)
      ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm (frame second))]
  simp
  rfl

theorem cutBulkMetricGramDeterminant_ambientPullback
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (frame : Fin 4 → AmbientTangentFiber period hPeriod point) :
    (cutBulkMetricGramMatrix period hPeriod
        (cutBulkAmbientSmoothGeneralLorentzMetricPullback period hPeriod metric)
        point (cutBulkAmbientFramePullback period hPeriod point frame)).det =
      (metricGramMatrix period hPeriod metric
        (cutBulkToAmbient period hPeriod point) frame).det := by
  rw [cutBulkMetricGramMatrix_ambientPullback period hPeriod metric point frame]

/-- The absolute metric density is unchanged by simultaneous metric/frame
pullback to the cut bulk. -/
theorem cutBulkMetricVolumeDensity_ambientPullback
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (frame : Fin 4 → AmbientTangentFiber period hPeriod point) :
    cutBulkMetricVolumeDensity period hPeriod
        (cutBulkAmbientSmoothGeneralLorentzMetricPullback period hPeriod metric)
        point (cutBulkAmbientFramePullback period hPeriod point frame) =
      metricVolumeDensity period hPeriod metric
        (cutBulkToAmbient period hPeriod point) frame := by
  unfold cutBulkMetricVolumeDensity metricVolumeDensity
  rw [cutBulkMetricGramDeterminant_ambientPullback period hPeriod metric point frame]

end
end P0EFTJanusMappingTorusCutBulkMetricVolumeDensityNaturality4D
end JanusFormal

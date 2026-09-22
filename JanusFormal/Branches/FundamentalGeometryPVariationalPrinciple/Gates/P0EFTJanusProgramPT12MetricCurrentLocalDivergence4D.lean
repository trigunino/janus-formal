import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalCurrentLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

/-! Actual metric-density formula for the canonical metric-volume divergence. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

open P0EFTJanusProgramPT12CanonicalCurrentPullback4D
open P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D

open P0EFTJanusProgramPT12CanonicalCurrentLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D

theorem localDensityDivergence_weight_transfer
    (density weight : Vector4 → Real) (field : Vector4 → Vector4) (coordinate : Vector4) :
    holonomicLocalDensityDivergence density
        (fun current => weight current • field current) coordinate / weight coordinate =
      holonomicLocalDensityDivergence (fun current => density current * weight current)
        field coordinate := by
  unfold holonomicLocalDensityDivergence
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, div_div]

theorem pulledCurrent_smoothScalarMul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (scalar : SmoothScalarField period hPeriod) (vector : SmoothTangentField period hPeriod)
    (coordinate : Vector4) :
    pulledRegularFrameExpansion period hPeriod metric patch
        (smoothScalarSMulTangentField period hPeriod scalar vector) coordinate =
      scalar (patch.coordinateMap coordinate) •
        pulledRegularFrameExpansion period hPeriod metric patch vector coordinate := by
  simp only [pulledRegularFrameExpansion, regularFrameCanonicalCoefficient_smul,
    P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D.smoothScalarFieldMul_apply,
    mul_smul, Finset.smul_sum]

/-- Intrinsic density times the pulled relative density is the supplied metric density. -/
theorem localDensity_mul_pulledMetricRatio
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    localMetricVolumeFactor period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate *
      globalMetricVolumeRatio period hPeriod metric (patch.coordinateMap coordinate) =
    localMetricVolumeFactor period hPeriod metric patch coordinate := by
  rw [globalMetricVolumeRatio_eq_local]
  unfold localMetricVolumeRatio
  exact mul_div_cancel₀ _ (localMetricVolumeFactor_ne_zero period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

/-- Weighted canonical divergence is the actual local metric-density divergence. -/
theorem metricCurrentDivergence_eq_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod) (coordinate : Vector4) :
    canonicalMetricVolumeDivergence period hPeriod metric vector (patch.coordinateMap coordinate) =
      holonomicLocalDensityDivergence (localMetricVolumeFactor period hPeriod metric.metric patch)
        (pulledRegularFrameExpansion period hPeriod metric patch vector) coordinate := by
  change canonicalTenFlowDivergence period hPeriod metric
    (canonicalMetricVolumeCurrent period hPeriod metric vector) (patch.coordinateMap coordinate) /
      globalMetricVolumeRatio period hPeriod metric.metric (patch.coordinateMap coordinate) = _
  rw [canonicalCurrentDivergence_eq_local]
  have hCurrent : pulledRegularFrameExpansion period hPeriod metric patch
      (canonicalMetricVolumeCurrent period hPeriod metric vector) = fun current =>
      globalMetricVolumeRatio period hPeriod metric.metric (patch.coordinateMap current) •
        pulledRegularFrameExpansion period hPeriod metric patch vector current := by
    funext current
    exact pulledCurrent_smoothScalarMul period hPeriod metric patch
      (globalSmoothMetricVolumeRatio period hPeriod metric.metric) vector current
  rw [hCurrent, localDensityDivergence_weight_transfer]
  have hDensity : (fun current => localMetricVolumeFactor period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current *
      globalMetricVolumeRatio period hPeriod metric.metric (patch.coordinateMap current)) =
      localMetricVolumeFactor period hPeriod metric.metric patch := by
    funext current
    exact localDensity_mul_pulledMetricRatio period hPeriod metric.metric patch current
  rw [hDensity]

end
end P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D
end JanusFormal

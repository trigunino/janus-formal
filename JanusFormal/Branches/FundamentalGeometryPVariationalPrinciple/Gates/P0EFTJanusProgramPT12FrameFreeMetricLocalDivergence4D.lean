import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeCurrentLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMetricDivergenceStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalCurrentLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

/-! Actual metric-density formula for the canonical metric-volume divergence. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FrameFreeMetricLocalDivergence4D

set_option autoImplicit false


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

open P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D
open P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
open P0EFTJanusProgramPT12FrameFreeCurrentLocalDivergence4D
open P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D
open P0EFTJanusProgramPT12FrameFreeMetricDivergenceStokes4D

theorem frameFreeCurrentPullback_smoothScalarMul
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (scalar : SmoothScalarField period hPeriod) (vector : SmoothTangentField period hPeriod)
    (coordinate : Vector4) :
    frameFreeCurrentPullback period hPeriod patch
        (smoothScalarSMulTangentField period hPeriod scalar vector) coordinate =
      scalar (patch.coordinateMap coordinate) •
        frameFreeCurrentPullback period hPeriod patch vector coordinate := by
  simp only [frameFreeCurrentPullback_apply]
  exact (frameFreeCoordinateDerivativeEquiv period hPeriod patch coordinate).symm.map_smul
    (scalar (patch.coordinateMap coordinate)) (vector (patch.coordinateMap coordinate))
/-- Weighted canonical divergence is the actual local metric-density divergence. -/
theorem frameFreeMetricCurrentDivergence_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod) (coordinate : Vector4) :
    frameFreeMetricVolumeDivergence period hPeriod metric vector (patch.coordinateMap coordinate) =
      holonomicLocalDensityDivergence (localMetricVolumeFactor period hPeriod metric patch)
        (frameFreeCurrentPullback period hPeriod patch vector) coordinate := by
  change frameFreeTenFlowDivergence period hPeriod metric
    (frameFreeMetricVolumeCurrent period hPeriod metric vector) (patch.coordinateMap coordinate) /
      globalMetricVolumeRatio period hPeriod metric (patch.coordinateMap coordinate) = _
  rw [frameFreeCurrentDivergence_eq_local]
  have hCurrent : frameFreeCurrentPullback period hPeriod patch
      (frameFreeMetricVolumeCurrent period hPeriod metric vector) = fun current =>
      globalMetricVolumeRatio period hPeriod metric (patch.coordinateMap current) •
        frameFreeCurrentPullback period hPeriod patch vector current := by
    funext current
    exact frameFreeCurrentPullback_smoothScalarMul period hPeriod patch
      (globalSmoothMetricVolumeRatio period hPeriod metric) vector current
  rw [hCurrent, localDensityDivergence_weight_transfer]
  have hDensity : (fun current => localMetricVolumeFactor period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current *
      globalMetricVolumeRatio period hPeriod metric (patch.coordinateMap current)) =
      localMetricVolumeFactor period hPeriod metric patch := by
    funext current
    exact localDensity_mul_pulledMetricRatio period hPeriod metric patch current
  rw [hDensity]

end
end P0EFTJanusProgramPT12FrameFreeMetricLocalDivergence4D
end JanusFormal

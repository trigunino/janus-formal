import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2EinsteinHilbertVolumeResidualBridge4D

/-! # Complete mobile-volume Einstein--Hilbert residual bridge -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2MobileEinsteinHilbertResidualBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 6000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertFrozenVolumeDecomposition4D
open P0EFTJanusFiniteFrameRegularC2FrozenEinsteinHilbertDerivativeBridge4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertVolumeDefectDerivative4D
open P0EFTJanusFiniteFrameRegularC2EinsteinHilbertVolumeResidualBridge4D
open P0EFTJanusStoredVolumePalatiniMetricResidual4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Stored-volume curvature residual plus the exact moving-volume trace term. -/
def regularFrameMobileEinsteinHilbertResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothSymmetricTensorAdd period hPeriod
    (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod metric
      couplings.gravitationalCoupling)
    (finiteFrameEinsteinHilbertMobileVolumeResidual period hPeriod metric couplings)

theorem regularFrameMobileEinsteinHilbertResidual_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameMobileEinsteinHilbertResidual period hPeriod metric couplings) tensor point =
      generalMetricTensorPairingAt period hPeriod metric.metric
          (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod metric
            couplings.gravitationalCoupling) tensor point +
        generalMetricTensorPairingAt period hPeriod metric.metric
          (finiteFrameEinsteinHilbertMobileVolumeResidual period hPeriod metric couplings)
          tensor point := by
  unfold regularFrameMobileEinsteinHilbertResidual
  exact generalMetricTensorPairingAt_add_left period hPeriod metric.metric _ _ tensor point

/-- The full mobile finite EH Euler is represented by one smooth tensor residual
on every smooth direction in canonical-volume gauge. -/
theorem finiteFrameC2EinsteinHilbertEuler_zero_smooth_lift_eq_mobileResidualPairing
    (frame : SmoothD8Frame period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    finiteFrameC2EinsteinHilbertEuler period hPeriod frame metric.metric couplings 0
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameMobileEinsteinHilbertResidual period hPeriod metric couplings)
        tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let direction :=
    smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor
  have hZero : (0 : GeneralMetricRelativeC2Core period hPeriod frame metric.metric) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame metric.metric :=
    zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame metric.metric
  have hSplit := congrArg (fun derivative :
      GeneralMetricRelativeC2Core period hPeriod frame metric.metric →L[Real] Real =>
        derivative direction)
    (finiteFrameC2EinsteinHilbertEuler_eq_frozen_add_volumeDefect period hPeriod frame
      metric.metric couplings 0 hZero)
  simp only [add_apply] at hSplit
  rw [hSplit]
  rw [finiteFrameC2FrozenVolumeEinsteinHilbertEuler_zero_smooth_eq_storedVolumeResidualPairing
      period hPeriod metric hCanonicalVolume frame tensor couplings,
    finiteFrameC2EinsteinHilbertVolumeDefectEuler_zero_smooth_lift_eq_residualPairing
      period hPeriod frame metric hCanonicalVolume couplings tensor]
  have hStored :=
    (generalMetricTensorPairingAt_continuous period hPeriod metric.metric
      (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod metric
        couplings.gravitationalCoupling) tensor).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hVolume :=
    (generalMetricTensorPairingAt_continuous period hPeriod metric.metric
      (finiteFrameEinsteinHilbertMobileVolumeResidual period hPeriod metric couplings)
      tensor).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  rw [← integral_add hStored hVolume]
  apply integral_congr_ae
  filter_upwards [] with point
  exact (regularFrameMobileEinsteinHilbertResidual_pairing period hPeriod metric couplings tensor
    point).symm

end
end P0EFTJanusFiniteFrameRegularC2MobileEinsteinHilbertResidualBridge4D
end JanusFormal

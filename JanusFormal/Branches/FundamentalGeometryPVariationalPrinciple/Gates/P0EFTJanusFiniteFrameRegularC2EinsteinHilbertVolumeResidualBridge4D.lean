import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2EinsteinHilbertVolumeDefectDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2CanonicalVolumeDerivativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D

/-! # Tensor residual for the mobile-volume Einstein--Hilbert defect -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2EinsteinHilbertVolumeResidualBridge4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameC2ProjectedScalarGlobalAgreement4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertFrozenVolumeDecomposition4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertVolumeDefectDerivative4D
open P0EFTJanusFiniteFrameRegularC2CanonicalVolumeDerivativeBridge4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

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

/-- Smooth coefficient multiplying the metric in the mobile-volume EH residual. -/
def finiteFrameEinsteinHilbertMobileVolumeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) : SmoothScalarField period hPeriod where
  toFun := fun point =>
    (1 / 2) * metric.volume point *
      ((1 / (2 * couplings.gravitationalCoupling)) *
        (globalSmoothScalarCurvature period hPeriod metric.metric point -
          2 * couplings.cosmologicalConstant))
  contMDiff_toFun :=
    (contMDiff_const.mul metric.volume.contMDiff_toFun).mul
      (contMDiff_const.mul
        ((globalSmoothScalarCurvature period hPeriod metric.metric).contMDiff_toFun.sub
          contMDiff_const))

/-- Pure trace metric residual contributed by the moving EH volume. -/
def finiteFrameEinsteinHilbertMobileVolumeResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothBulkScalarSMulTensor period hPeriod
    (finiteFrameEinsteinHilbertMobileVolumeCoefficient period hPeriod metric couplings)
    metric.metric.tensor

theorem finiteFrameEinsteinHilbertMobileVolumeResidual_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (finiteFrameEinsteinHilbertMobileVolumeResidual period hPeriod metric couplings)
        tensor point =
      (metric.volume point / 2 *
        generalMetricTensorPairingAt period hPeriod metric.metric metric.metric.tensor tensor point) *
      ((1 / (2 * couplings.gravitationalCoupling)) *
        (globalSmoothScalarCurvature period hPeriod metric.metric point -
          2 * couplings.cosmologicalConstant)) := by
  unfold finiteFrameEinsteinHilbertMobileVolumeResidual
  rw [generalMetricTensorPairingAt_symmetric,
    generalMetricTensorPairingAt_smoothBulkScalarSMul_right,
    generalMetricTensorPairingAt_symmetric]
  unfold finiteFrameEinsteinHilbertMobileVolumeCoefficient
  ring

theorem finiteFrameC2EinsteinHilbertScalarFactor_zero_smooth_regular
    (frame : SmoothD8Frame period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameC2EinsteinHilbertScalarFactor period hPeriod frame metric.metric couplings 0 point =
      (1 / (2 * couplings.gravitationalCoupling)) *
        (globalSmoothScalarCurvature period hPeriod metric.metric point -
          2 * couplings.cosmologicalConstant) := by
  have hAgreement :=
    finiteFrameProjectedScalarCurvatureC0_smooth_eq_global period hPeriod frame metric.metric
      metric.metric 0 (by simp)
        (by simpa only [map_zero] using
          zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric.metric)
  have hAgreement' :
      finiteFrameProjectedScalarCurvatureC0 period hPeriod frame metric.metric 0 =
        smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (globalSmoothScalarCurvature period hPeriod metric.metric) := by
    simpa only [map_zero] using hAgreement
  have hAt := congrArg (fun field : C0Scalar period hPeriod => field point) hAgreement'
  unfold finiteFrameC2EinsteinHilbertScalarFactor
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul,
    finiteFrameC0Constant, ContinuousMap.coe_mk]
  rw [hAt]
  rfl

/-- On every smooth lift in canonical-volume gauge, the exact finite EH volume
defect derivative is the pairing with its pure trace residual. -/
theorem finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero_smooth_lift_eq_residualPairing
    (frame : SmoothD8Frame period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero period hPeriod frame metric.metric
        couplings
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (finiteFrameEinsteinHilbertMobileVolumeResidual period hPeriod metric couplings)
        tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [finiteFrameCanonicalVolumeC0DerivativeAtZero_smooth_lift_regular period hPeriod frame
      metric hCanonicalVolume tensor point,
    finiteFrameC2EinsteinHilbertScalarFactor_zero_smooth_regular period hPeriod frame metric
      couplings point,
    finiteFrameEinsteinHilbertMobileVolumeResidual_pairing period hPeriod metric couplings tensor
      point]

/-- The actual finite volume-defect Euler has the same residual pairing. -/
theorem finiteFrameC2EinsteinHilbertVolumeDefectEuler_zero_smooth_lift_eq_residualPairing
    (frame : SmoothD8Frame period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    finiteFrameC2EinsteinHilbertVolumeDefectEuler period hPeriod frame metric.metric couplings 0
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (finiteFrameEinsteinHilbertMobileVolumeResidual period hPeriod metric couplings)
        tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [finiteFrameC2EinsteinHilbertVolumeDefectEuler_zero_eq_explicit]
  exact finiteFrameC2EinsteinHilbertVolumeDefectDerivativeAtZero_smooth_lift_eq_residualPairing
    period hPeriod frame metric hCanonicalVolume couplings tensor

end
end P0EFTJanusFiniteFrameRegularC2EinsteinHilbertVolumeResidualBridge4D
end JanusFormal

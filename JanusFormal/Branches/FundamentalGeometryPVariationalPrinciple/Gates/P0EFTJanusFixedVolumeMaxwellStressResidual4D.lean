import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D

/-! # Smooth residual of the fixed-volume Maxwell metric term

The variable-volume stress and the positive fixed-volume correction are
represented by `(volume / 2) T + (volume F² / 8) g`. The volume is the stored
base volume, and the integration measure is the canonical Lorentz measure.
This gate does not include the separately induced gauge variation.
-/

namespace JanusFormal
namespace P0EFTJanusFixedVolumeMaxwellStressResidual4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
open P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The trace of the actual smooth C² direction is the invariant metric pairing. -/
theorem regularGeneralMetricC2RelativeMatrixAt_smooth_trace_eq_metricPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Matrix.trace (regularGeneralMetricC2RelativeMatrixAt period hPeriod metric
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point) =
      generalMetricTensorPairingAt period hPeriod metric.metric
        metric.metric.tensor tensor point := by
  let basis := regularMetricBasisAt period hPeriod metric point
  have hMatrix :
      regularGeneralMetricC2RelativeMatrixAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point =
        LinearMap.toMatrix basis basis
          (raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point).toLinearMap := by
    ext row column
    change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor row column)) point = _
    rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    change smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor row column point = _
    rw [smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply,
      finiteFrameEndomorphismMatrixAt_apply,
      regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate,
      LinearMap.toMatrix_apply]
    change (metric.frameEquiv point).symm
        (raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point
          (metric.frame column point)) row =
      basis.repr
        (raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point
          (basis column)) row
    rw [show basis column = metric.frame column point from
      regularMetricBasisAt_apply period hPeriod metric point column]
    rfl
  rw [hMatrix, ← LinearMap.trace_eq_matrix_trace Real basis]
  exact (generalMetricTensorTraceAt_eq_pairing_metric period hPeriod
    metric.metric tensor point).trans
      (generalMetricTensorPairingAt_symmetric period hPeriod
        metric.metric tensor metric.metric.tensor point)

/-- The completed volume velocity on smooth tests is half the metric pairing. -/
theorem regularGeneralMetricC2VolumeDerivativeAtZero_smooth_eq_metricPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)) point =
      metric.volume point / 2 *
        generalMetricTensorPairingAt period hPeriod metric.metric
          metric.metric.tensor tensor point := by
  change regularGeneralMetricC0VolumeDerivativeAtZero period hPeriod metric
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point = _
  rw [regularGeneralMetricC0VolumeDerivativeAtZero_valueAt,
    regularGeneralMetricC2RelativeMatrixAt_smooth_trace_eq_metricPairing]

/-- Explicit smooth tensor for the stress and the positive volume correction. -/
def regularFrameFixedVolumeMaxwellStressResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothSymmetricTensorAdd period hPeriod
    (smoothBulkScalarSMulTensor period hPeriod ((1 / 2 : Real) • metric.volume)
      (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential))
    (smoothBulkScalarSMulTensor period hPeriod
      ((1 / 8 : Real) • smoothScalarFieldMul period hPeriod metric.volume
        (globalSmoothMaxwellPairing period hPeriod metric.metric potential potential))
      metric.metric.tensor)

/-- Exact pointwise covector representation, retaining the positive correction. -/
theorem regularFrameFixedVolumeMaxwellStressResidual_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameFixedVolumeMaxwellStressResidual period hPeriod metric potential)
        tensor point =
      metric.volume point / 2 * generalMetricTensorPairingAt period hPeriod metric.metric
        (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential) tensor point +
      metric.volume point * globalMaxwellPairing period hPeriod metric.metric
          potential potential point / 8 *
        generalMetricTensorPairingAt period hPeriod metric.metric
          metric.metric.tensor tensor point := by
  unfold regularFrameFixedVolumeMaxwellStressResidual
  rw [generalMetricTensorPairingAt_symmetric, generalMetricTensorPairingAt_add_right,
    generalMetricTensorPairingAt_smoothBulkScalarSMul_right,
    generalMetricTensorPairingAt_smoothBulkScalarSMul_right,
    generalMetricTensorPairingAt_symmetric period hPeriod metric.metric tensor,
    generalMetricTensorPairingAt_symmetric period hPeriod metric.metric tensor]
  change (1 / 2 : Real) * metric.volume point * _ +
      ((1 / 8 : Real) * (metric.volume point *
        globalMaxwellPairing period hPeriod metric.metric potential potential point)) * _ = _
  ring

/-- Positive fixed-volume correction in the same canonical measure. -/
theorem regularGeneralMetricC2FixedVolumeMaxwellCorrection_smooth_eq_metricIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2FixedVolumeMaxwellCorrection period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) potential
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point, metric.volume point * globalMaxwellPairing period hPeriod metric.metric
          potential potential point / 8 *
        generalMetricTensorPairingAt period hPeriod metric.metric metric.metric.tensor tensor point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [regularGeneralMetricC2FixedVolumeMaxwellCorrection_eq_integral]
  apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
    ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  funext point
  rw [regularGeneralMetricC2VolumeDerivativeAtZero_smooth_eq_metricPairing]
  ring

/-- The entire fixed-frame metric term is the canonical integral of one smooth tensor. -/
theorem regularFrameMaxwellStress_add_fixedVolumeCorrection_eq_residualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (∫ point, metric.volume point / 2 * generalMetricTensorPairingAt period hPeriod
      metric.metric (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
      regularGeneralMetricC2FixedVolumeMaxwellCorrection period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) potential
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameFixedVolumeMaxwellStressResidual period hPeriod metric potential)
        tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  have hStress : Continuous (fun point : EffectiveQuotient period hPeriod =>
      metric.volume point / 2 * generalMetricTensorPairingAt period hPeriod metric.metric
        (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential) tensor point) :=
    (metric.volume.contMDiff_toFun.continuous.div_const 2).mul
    (generalMetricTensorPairingAt_continuous period hPeriod metric.metric
      (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential) tensor)
  have hCurvature : Continuous (globalMaxwellPairing period hPeriod metric.metric
      potential potential) :=
    (globalSmoothMaxwellPairing period hPeriod metric.metric potential potential).contMDiff_toFun.continuous
  have hCorrection : Continuous (fun point : EffectiveQuotient period hPeriod =>
      metric.volume point * globalMaxwellPairing period hPeriod metric.metric
        potential potential point / 8 *
        generalMetricTensorPairingAt period hPeriod metric.metric metric.metric.tensor tensor point) :=
    ((metric.volume.contMDiff_toFun.continuous.mul hCurvature).div_const 8).mul
    (generalMetricTensorPairingAt_continuous period hPeriod metric.metric metric.metric.tensor tensor)
  rw [regularGeneralMetricC2FixedVolumeMaxwellCorrection_smooth_eq_metricIntegral,
    ← integral_add (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (hStress.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hCorrection.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
    ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  funext point
  exact (regularFrameFixedVolumeMaxwellStressResidual_pairing
    period hPeriod metric potential tensor point).symm

/-- Native fixed-volume Maxwell derivative represented on genuine smooth tests. -/
theorem regularGeneralMetricC0FixedVolumeMaxwellAction_fderiv_zero_eq_residualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    fderiv Real (regularGeneralMetricC0FixedVolumeMaxwellAction period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) potential potential) 0
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameFixedVolumeMaxwellStressResidual period hPeriod metric potential)
        tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [regularGeneralMetricC0FixedVolumeMaxwellAction_fderiv_zero_eq_variable_add_correction,
    regularGeneralMetricC2IntegratedMaxwellActionDerivative_smooth_invariant]
  exact regularFrameMaxwellStress_add_fixedVolumeCorrection_eq_residualIntegral
    period hPeriod metric potential tensor

end
end P0EFTJanusFixedVolumeMaxwellStressResidual4D
end JanusFormal

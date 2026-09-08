import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2MobileInteractionDerivativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameMetricTensorTrace4D

/-! # Finite-frame/regular bridge for the canonical volume derivative -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2CanonicalVolumeDerivativeBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 4000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-- The completed redundant-frame trace of a smooth lift is the intrinsic
metric contraction, independently of the chosen finite frame. -/
theorem c2FiniteMatrixTrace_smoothToGeneralMetricRelativeC2Core_valueAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2FiniteMatrixTrace period hPeriod frame.count
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor).1) point =
      generalMetricTensorPairingAt period hPeriod metric metric.tensor tensor point := by
  have hTraceValue :
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (c2FiniteMatrixTrace period hPeriod frame.count
            (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor).1) point =
        Matrix.trace (c2FiniteMatrixValueAt period hPeriod frame.count
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor).1 point) := by
    rw [c2FiniteMatrixTrace_apply]
    let evaluate : C0Scalar period hPeriod →ₗ[Real] Real :=
      { toFun := fun value => value point
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    change evaluate ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)
        (∑ index : Fin frame.count,
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor).1 index index)) =
      ∑ index : Fin frame.count,
        evaluate ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)
          ((smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor).1 index index))
    rw [map_sum, map_sum]
  rw [hTraceValue]
  have hValue :
      c2FiniteMatrixValueAt period hPeriod frame.count
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor).1 point =
        finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
          (raisedGeneralMetricTensorAt period hPeriod metric tensor point) := by
    ext row column
    change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor
            row column)) point = _
    rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    exact congrFun (congrFun
      (smoothGeneralMetricRelativeEndomorphismMatrix_apply period hPeriod frame metric tensor point)
      row) column
  rw [hValue, finiteFrameEndomorphismMatrixAt_trace]
  change generalMetricTensorTraceAt period hPeriod metric tensor point = _
  rw [generalMetricTensorTraceAt_eq_pairing_metric,
    generalMetricTensorPairingAt_symmetric]

/-- In canonical-volume gauge, the finite derivative of the volume coefficient
on a smooth lift is the regular half-trace density. -/
theorem finiteFrameCanonicalVolumeC0DerivativeAtZero_smooth_lift_regular
    (frame : SmoothD8Frame period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame metric.metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) point =
      metric.volume point / 2 *
        generalMetricTensorPairingAt period hPeriod metric.metric metric.metric.tensor tensor point := by
  rw [finiteFrameCanonicalVolumeC0DerivativeAtZero_apply, ContinuousMap.mul_apply]
  change globalMetricVolumeRatio period hPeriod metric.metric point *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        ((1 / 2 : Real) • c2FiniteMatrixTrace period hPeriod frame.count
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor).1) point = _
  rw [c2ScalarSmul_valueAt,
    c2FiniteMatrixTrace_smoothToGeneralMetricRelativeC2Core_valueAt]
  have hVolume := congrArg
    (fun field : SmoothScalarField period hPeriod => field point) hCanonicalVolume
  change metric.volume point =
    globalMetricVolumeRatio period hPeriod metric.metric point at hVolume
  rw [← hVolume]
  ring

end
end P0EFTJanusFiniteFrameRegularC2CanonicalVolumeDerivativeBridge4D
end JanusFormal

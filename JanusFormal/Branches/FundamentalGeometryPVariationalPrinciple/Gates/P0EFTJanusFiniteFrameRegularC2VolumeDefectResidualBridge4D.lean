import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2SpectralPotentialValueBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionSmoothMetricResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D

/-! # Tensor residual for the mobile-volume interaction defect -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2VolumeDefectResidualBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 6000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Matrix.Norms.Frobenius
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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D
open P0EFTJanusFiniteFrameC2InteractionVolumeDefectDerivative4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameRegularC2CanonicalVolumeDerivativeBridge4D
open P0EFTJanusFiniteFrameRegularC2SpectralPotentialValueBridge4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusPairedInteractionRecenterValue4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

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
@[reducible] local instance : NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance : AddCommGroup Matrix4 := inferInstance
local instance : PseudoMetricSpace Matrix4 := inferInstance
local instance : UniformSpace Matrix4 := inferInstance
local instance : TopologicalSpace Matrix4 := inferInstance
@[reducible] local instance : NormedSpace Real Matrix4 := NormedAlgebra.toNormedSpace Matrix4
local instance : Module Real Matrix4 := inferInstance
local instance : CompleteSpace Matrix4 := FiniteDimensional.complete Real Matrix4

private theorem generalMetricTensorPairingAt_zeroSymmetric_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric
        (zeroSymmetricTensor period hPeriod) variation point = 0 := by
  have hRaised : raisedGeneralMetricTensorAt period hPeriod metric
      (zeroSymmetricTensor period hPeriod) point = 0 := by
    apply ContinuousLinearMap.ext
    intro vector
    simp [raisedGeneralMetricTensorAt, zeroSymmetricTensor]
  unfold generalMetricTensorPairingAt
  rw [hRaised]
  simp

/-- Smooth coefficient multiplying the plus metric in the mobile-volume
residual. -/
def pairedInteractionMobileVolumeCoefficient
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    (-interactionScale / 2) * plusBase.volume point *
      matrixSpectralPotential coefficients
        (pairedInteractionCenterRoot period hPeriod plusBase minusBase point)
  contMDiff_toFun :=
    (contMDiff_const.mul plusBase.volume.contMDiff_toFun).mul
      ((matrixSpectralPotential_contDiff coefficients).contMDiff.comp
        (regularGeneralMetricC2IdentityRootMatrixAt_contMDiff period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hRoot))

/-- The mobile-volume defect is represented by a pure plus-sector metric
residual. -/
def pairedInteractionMobileVolumeResidualPair
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothSymmetricCovariantTwoTensor period hPeriod :=
  (smoothBulkScalarSMulTensor period hPeriod
      (pairedInteractionMobileVolumeCoefficient period hPeriod plusBase minusBase hRoot
        interactionScale coefficients)
      plusBase.metric.tensor,
    zeroSymmetricTensor period hPeriod)

/-- Pointwise pairing of the volume residual is the central potential times
the regular half-trace volume derivative. -/
theorem pairedInteractionMobileVolumeResidualPair_plus_pairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod plusBase.metric
        (pairedInteractionMobileVolumeResidualPair period hPeriod plusBase minusBase hRoot
          interactionScale coefficients).1 variation point =
      (-interactionScale) *
        (plusBase.volume point / 2 *
          generalMetricTensorPairingAt period hPeriod plusBase.metric
            plusBase.metric.tensor variation point) *
        matrixSpectralPotential coefficients
          (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) := by
  unfold pairedInteractionMobileVolumeResidualPair
  rw [generalMetricTensorPairingAt_symmetric,
    generalMetricTensorPairingAt_smoothBulkScalarSMul_right,
    generalMetricTensorPairingAt_symmetric]
  unfold pairedInteractionMobileVolumeCoefficient
  ring

/-- Pointwise integral formula for the finite mobile-volume defect
derivative. -/
theorem pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (direction : PairedFiniteFrameMetricC2Core period hPeriod geometry frame) :
    pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero period hPeriod geometry frame
        hRegular interactionScale coefficients direction =
      ∫ point, (-interactionScale) *
        finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame geometry.plusMetric
          direction.1 point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular
            coefficients 0) point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero
    pairedFiniteFrameCanonicalVolumeDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply, finiteFrameBRSTCanonicalIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst']
  ring

/-- On common smooth lifts, the exact finite mobile-volume defect is the
pairing with its smooth pure plus-sector metric residual. -/
theorem pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero_smooth_lifts_eq_metricResidualPairing
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    let finiteDirection :=
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
        smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation)
    pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero period hPeriod geometry frame
        hFiniteRegular interactionScale coefficients finiteDirection =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (pairedInteractionMobileVolumeResidualPair period hPeriod plusBase minusBase hRoot
          interactionScale coefficients)
        (globalMinimalPhysicalMetricTestOfPair period hPeriod
          (plusVariation, minusVariation)) := by
  dsimp only
  rw [pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero_apply]
  unfold regularGeneralMetricC2PairedMetricResidualPairing
  rw [globalMinimalPhysicalMetricTestPair_ofPair]
  unfold canonicalGeneralMetricTensorPairPairing
  apply integral_congr_ae
  filter_upwards [] with point
  rw [finiteFrameCanonicalVolumeC0DerivativeAtZero_apply, ContinuousMap.mul_apply]
  simp only [regularGeneralMetricC2LorentzChartGeometry_plusMetric]
  change (-interactionScale) *
      (globalMetricVolumeRatio period hPeriod plusBase.metric point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          ((1 / 2 : Real) • c2FiniteMatrixTrace period hPeriod frame.count
            (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
              plusVariation).1) point) *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotential period hPeriod frame
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
          (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
            plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
          coefficients 0) point = _
  rw [c2ScalarSmul_valueAt,
    c2FiniteMatrixTrace_smoothToGeneralMetricRelativeC2Core_valueAt]
  have hVolume := congrArg
    (fun field : SmoothScalarField period hPeriod => field point) hCanonicalVolume
  change plusBase.volume point =
    globalMetricVolumeRatio period hPeriod plusBase.metric point at hVolume
  rw [← hVolume]
  rw [pairedFiniteFrameC2SpectralPotential_zero_regular_valueAt period hPeriod coefficients
    plusBase minusBase hChart frame point]
  have hRootValue :
      c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0) point =
        pairedInteractionCenterRoot period hPeriod plusBase minusBase point := by
    unfold regularGeneralMetricC2PairedRelativeRoot
    rw [pairedInteractionRelativeMatrix_zero]
    rfl
  rw [hRootValue]
  unfold generalMetricTensorPairPairingAt
  rw [pairedInteractionMobileVolumeResidualPair_plus_pairing]
  simp only [pairedInteractionMobileVolumeResidualPair]
  rw [generalMetricTensorPairingAt_zeroSymmetric_left, add_zero]
  ring

end
end P0EFTJanusFiniteFrameRegularC2VolumeDefectResidualBridge4D
end JanusFormal

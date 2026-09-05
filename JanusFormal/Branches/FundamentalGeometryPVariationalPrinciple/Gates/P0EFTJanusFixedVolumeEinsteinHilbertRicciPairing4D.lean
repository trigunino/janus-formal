import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D

/-! # Ricci pairing for the fixed-volume Einstein--Hilbert derivative

The half-trace volume correction cancels the scalar-curvature and
cosmological metric terms in the Einstein pairing. The result pairs Ricci
with the inverse-metric velocity, with positive coefficient (1/(2κ)).
Canonical-volume gauge is required only at the base metric.
-/

namespace JanusFormal
namespace P0EFTJanusFixedVolumeEinsteinHilbertRicciPairing4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D

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
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The correction is the scalar Lagrangian times the genuine half-trace
volume variation, without any volume-gauge hypothesis. -/
theorem regularFrameEinsteinHilbertVolumeCorrection_eq_halfTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularFrameEinsteinHilbertVolumeCorrection period hPeriod metric couplings tensor =
      ∫ point,
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 point -
            2 * couplings.cosmologicalConstant)) *
          (metric.volume point / 2 *
            Matrix.trace (regularFrameMetricInverseMatrixMap period hPeriod metric point *
              regularFrameCovariantVariationMatrixAt period hPeriod metric tensor point))
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold regularFrameEinsteinHilbertVolumeCorrection
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply, smul_eq_mul,
    regularGeneralMetricC0Constant, ContinuousMap.coe_mk]
  rw [regularGeneralMetricC0VolumeDerivativeAtZero_smooth]

private theorem tensorPairing_einstein_add_trace
    (metric inverse ricci velocity : Matrix (Fin 4) (Fin 4) Real)
    (cosmologicalConstant : Real) :
    tensorPairing velocity (einsteinTensorAt metric inverse ricci cosmologicalConstant) +
      ((scalarCurvatureAt inverse ricci - 2 * cosmologicalConstant) / 2) *
        tensorPairing velocity metric = tensorPairing velocity ricci := by
  calc
    _ = ∑ first : Index4, ∑ second : Index4,
        (velocity first second *
            einsteinTensorAt metric inverse ricci cosmologicalConstant first second +
          ((scalarCurvatureAt inverse ricci - 2 * cosmologicalConstant) / 2) *
            (velocity first second * metric first second)) := by
      simp only [tensorPairing, Finset.mul_sum, Finset.sum_add_distrib]
    _ = tensorPairing velocity ricci := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      dsimp only [einsteinTensorAt]
      ring

/-- The fixed-volume Ricci pairing uses the inverse-metric velocity. The
prefactor carries a plus sign; the covariant metric velocity has the opposite sign.
The definition contains no cosmological constant. -/
def regularFrameFixedVolumeEinsteinHilbertRicciPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  ∫ point, (1 / (2 * gravitationalCoupling)) *
    tensorPairing
      (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point)
      (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0 point)
    ∂(generalLorentzVolumeMeasure period hPeriod metric.metric)

/-- The volume correction cancels both metric-multiple terms in the
Einstein tensor and leaves exactly the Ricci contraction. -/
theorem regularFrameEinsteinHilbertInvariantBulk_sub_volumeCorrection_eq_ricciPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularFrameEinsteinHilbertInvariantBulk period hPeriod metric couplings tensor -
        regularFrameEinsteinHilbertVolumeCorrection period hPeriod metric couplings tensor =
      regularFrameFixedVolumeEinsteinHilbertRicciPairing period hPeriod metric
        couplings.gravitationalCoupling tensor := by
  let correction : C(EffectiveQuotient period hPeriod, Real) :=
    (((1 / (2 * couplings.gravitationalCoupling)) •
      (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 -
        regularGeneralMetricC0Constant period hPeriod
          (2 * couplings.cosmologicalConstant))) •
      regularGeneralMetricC0VolumeDerivativeAtZero period hPeriod metric
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor))
  have hBulk : Integrable
      (fun point => globalMetricVolumeRatio period hPeriod metric.metric point *
        (-(1 / (2 * couplings.gravitationalCoupling)) *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
              couplings.cosmologicalConstant) tensor point))
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
    exact ((globalMetricVolumeRatio_continuous period hPeriod metric.metric).mul
      ((generalMetricTensorPairingAt_continuous period hPeriod metric.metric
        (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
          couplings.cosmologicalConstant) tensor).const_mul _)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCorrection : Integrable correction
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    correction.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold regularFrameEinsteinHilbertInvariantBulk
    regularFrameEinsteinHilbertVolumeCorrection regularFrameFixedVolumeEinsteinHilbertRicciPairing
  rw [integral_generalLorentzVolumeMeasure_eq_reference,
    integral_generalLorentzVolumeMeasure_eq_reference, ← integral_sub hBulk hCorrection]
  apply integral_congr_ae
  filter_upwards [] with point
  have hGaugePoint : metric.volume point =
      globalMetricVolumeRatio period hPeriod metric.metric point :=
    congrArg (fun field => field point) hGauge
  have hVolume := regularGeneralMetricC0VolumeDerivativeAtZero_smooth_eq_inversePairing
    period hPeriod metric tensor point
  have hEinstein := regularGeneralMetricC0EinsteinInverseVelocity_pairing_invariant
    period hPeriod metric couplings.cosmologicalConstant tensor point
  have hScalar :
      regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 point =
        scalarCurvatureAt
          (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0 point)
          (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0 point) := rfl
  let velocity := regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
    (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point
  let base := regularFrameMetricMatrixMap period hPeriod metric point
  have hComm : tensorPairing base velocity = tensorPairing velocity base := by
    unfold tensorPairing
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    exact mul_comm _ _
  have hCancellation := tensorPairing_einstein_add_trace base
    (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0 point)
    (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0 point)
    velocity couplings.cosmologicalConstant
  have hWeighted := congrArg (fun value : Real =>
    globalMetricVolumeRatio period hPeriod metric.metric point *
      (1 / (2 * couplings.gravitationalCoupling)) * value) hCancellation
  rw [hEinstein] at hWeighted
  dsimp only [correction]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply, smul_eq_mul,
    regularGeneralMetricC0Constant, ContinuousMap.coe_mk]
  rw [hVolume, hGaugePoint, hScalar, hComm]
  linear_combination hWeighted

/-- The actual fixed-volume action derivative is the Ricci pairing. Only
the base metric satisfies canonical-volume gauge. -/
theorem regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ricciPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        couplings (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      regularFrameFixedVolumeEinsteinHilbertRicciPairing period hPeriod metric
        couplings.gravitationalCoupling tensor := by
  rw [regularFrameFixedVolumeEinsteinHilbertDerivative_invariantBulk_sub_volumeCorrection
    period hPeriod metric couplings tensor hGauge]
  exact regularFrameEinsteinHilbertInvariantBulk_sub_volumeCorrection_eq_ricciPairing
    period hPeriod metric couplings tensor hGauge

end
end P0EFTJanusFixedVolumeEinsteinHilbertRicciPairing4D
end JanusFormal

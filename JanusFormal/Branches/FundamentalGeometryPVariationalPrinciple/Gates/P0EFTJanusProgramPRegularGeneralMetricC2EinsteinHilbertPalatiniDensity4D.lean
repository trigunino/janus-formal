import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D

/-! # Einstein--Hilbert C² density in Einstein-plus-Palatini form -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Manifold ContDiff Topology BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Frobenius entry pairing is a trace after transposing the first matrix. -/
theorem tensorPairing_eq_trace_transpose_mul
    (first second : Matrix4) :
    tensorPairing first second = Matrix.trace (first.transpose * second) := by
  unfold tensorPairing Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Algebraic identity behind `δ√|g| = -√|g| g:δg⁻¹/2`. -/
theorem tensorPairing_neg_inverse_variation
    (metric inverse variation : Matrix4)
    (hSymmetric : metric.transpose = metric)
    (hInverse : metric * inverse = 1) :
    tensorPairing metric (-((inverse * variation) * inverse)) =
      -Matrix.trace (inverse * variation) := by
  rw [tensorPairing_eq_trace_transpose_mul, hSymmetric, Matrix.mul_neg,
    Matrix.trace_neg]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hInverse, one_mul,
    Matrix.trace_mul_comm]

/-- Pointwise C⁰ volume derivative in relative-matrix form. -/
theorem regularGeneralMetricC0VolumeDerivativeAtZero_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0VolumeDerivativeAtZero
        period hPeriod metric direction point =
      metric.volume point / 2 *
        Matrix.trace
          (regularGeneralMetricC2RelativeMatrixAt
            period hPeriod metric direction point) := by
  unfold regularGeneralMetricC0VolumeDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply]
  exact regularGeneralMetricC2VolumeDerivative_valueAt
    period hPeriod metric direction point

/-- The smooth half-trace volume formula. -/
theorem regularGeneralMetricC0VolumeDerivativeAtZero_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0VolumeDerivativeAtZero period hPeriod metric
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      metric.volume point / 2 *
        Matrix.trace
          (regularFrameMetricInverseMatrixMap period hPeriod metric point *
            regularFrameCovariantVariationMatrixAt
              period hPeriod metric tensor point) := by
  rw [regularGeneralMetricC0VolumeDerivativeAtZero_valueAt,
    regularGeneralMetricC2RelativeMatrixAt_smooth]

/-- The same volume velocity in the inverse-metric convention used by the
local Palatini theorem. -/
theorem regularGeneralMetricC0VolumeDerivativeAtZero_smooth_eq_inversePairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0VolumeDerivativeAtZero period hPeriod metric
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      -(metric.volume point / 2) *
        tensorPairing
          (regularFrameMetricMatrixMap period hPeriod metric point)
          (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
            (regularGeneralMetricC2SmoothDirection
              period hPeriod metric tensor) point) := by
  let base := regularFrameMetricMatrixMap period hPeriod metric point
  let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  let variation := regularFrameCovariantVariationMatrixAt
    period hPeriod metric tensor point
  have hSymmetric : base.transpose = base := by
    ext row column
    exact metric.metric.tensor.symmetric point _ _
  have hInverse : base * inverse = 1 := by
    exact Matrix.mul_nonsing_inv base
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hPairing := tensorPairing_neg_inverse_variation
    base inverse variation hSymmetric hInverse
  rw [regularGeneralMetricC0VolumeDerivativeAtZero_smooth,
    regularGeneralMetricC0InverseMetricVelocityAt_smooth]
  change metric.volume point / 2 * Matrix.trace (inverse * variation) =
    -(metric.volume point / 2) *
      tensorPairing base (-((inverse * variation) * inverse))
  rw [hPairing]
  ring

private theorem regularGeneralMetricC0Volume_zero_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0Volume period hPeriod metric 0 point =
      metric.volume point := by
  rw [regularGeneralMetricC0Volume_zero]
  rfl

private theorem regularGeneralMetricC0ScalarCurvature_zero_matrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 point =
      scalarCurvatureAt
        (regularGeneralMetricC0InverseMetricMatrixAt
          period hPeriod metric 0 point)
        (regularGeneralMetricC0RicciMatrixAt
          period hPeriod metric 0 point) := by
  unfold regularGeneralMetricC0ScalarCurvature scalarCurvatureAt tensorPairing
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    regularGeneralMetricC0InverseMetricMatrixAt,
    regularGeneralMetricC0RicciMatrixAt]

/-- Exact physical C² EH density derivative before removing the Palatini
divergence. -/
theorem regularGeneralMetricC0EinsteinHilbertDensityDerivative_smooth_palatini
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      (metric.volume point / (2 * couplings.gravitationalCoupling)) *
        (tensorPairing
            (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod
              metric
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor) point)
            (einsteinTensorAt
              (regularFrameMetricMatrixMap period hPeriod metric point)
              (regularGeneralMetricC0InverseMetricMatrixAt
                period hPeriod metric 0 point)
              (regularGeneralMetricC0RicciMatrixAt
                period hPeriod metric 0 point)
              couplings.cosmologicalConstant) +
          palatiniScalarVelocity
            (regularGeneralMetricC0InverseMetricMatrixAt
              period hPeriod metric 0 point)
            (regularGeneralMetricC0RicciVelocityAt period hPeriod metric
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor) point)) := by
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  let base := regularFrameMetricMatrixMap period hPeriod metric point
  let inverse := regularGeneralMetricC0InverseMetricMatrixAt
    period hPeriod metric 0 point
  let ricci := regularGeneralMetricC0RicciMatrixAt
    period hPeriod metric 0 point
  let inverseVelocity := regularGeneralMetricC0InverseMetricVelocityAt
    period hPeriod metric direction point
  let ricciVelocity := regularGeneralMetricC0RicciVelocityAt
    period hPeriod metric direction point
  let volumeVelocity := regularGeneralMetricC0VolumeDerivativeAtZero
    period hPeriod metric direction point
  have hDensityMap :=
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero_apply
      period hPeriod metric couplings direction
  have hDensity := congrArg
    (fun field : C0Scalar period hPeriod => field point) hDensityMap
  have hScalar :=
    regularGeneralMetricC0ScalarCurvatureDerivativeAtZero_pointwise
      period hPeriod metric direction point
  have hBaseVolume := regularGeneralMetricC0Volume_zero_valueAt
    period hPeriod metric point
  have hBaseScalar := regularGeneralMetricC0ScalarCurvature_zero_matrixAt
    period hPeriod metric point
  have hAsVelocity :
      regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
          period hPeriod metric couplings direction point =
        einsteinHilbertDensityVelocity couplings.gravitationalCoupling
          couplings.cosmologicalConstant (metric.volume point) volumeVelocity
          inverse ricci inverseVelocity ricciVelocity := by
    simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply,
      ContinuousMap.sub_apply, ContinuousMap.mul_apply, smul_eq_mul,
      regularGeneralMetricC0Constant] at hDensity
    rw [hBaseVolume, hBaseScalar, hScalar] at hDensity
    rw [hDensity]
    unfold einsteinHilbertDensityVelocity
    dsimp [inverse, ricci, inverseVelocity, ricciVelocity, volumeVelocity]
    ring
  rw [hAsVelocity]
  have hVolumeVelocity : volumeVelocity =
      -(metric.volume point / 2) * tensorPairing base inverseVelocity := by
    exact regularGeneralMetricC0VolumeDerivativeAtZero_smooth_eq_inversePairing
      period hPeriod metric tensor point
  rw [hVolumeVelocity]
  exact einsteinHilbertDensityVelocity_eq_einstein_add_palatini
    couplings.gravitationalCoupling couplings.cosmologicalConstant
      (metric.volume point) base inverse ricci inverseVelocity ricciVelocity

/-- Integrated EH derivative with its derived Einstein and Palatini terms. -/
theorem regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_palatini
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      ∫ point,
        (metric.volume point / (2 * couplings.gravitationalCoupling)) *
          (tensorPairing
              (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod
                metric
                (regularGeneralMetricC2SmoothDirection
                  period hPeriod metric tensor) point)
              (einsteinTensorAt
                (regularFrameMetricMatrixMap period hPeriod metric point)
                (regularGeneralMetricC0InverseMetricMatrixAt
                  period hPeriod metric 0 point)
                (regularGeneralMetricC0RicciMatrixAt
                  period hPeriod metric 0 point)
                couplings.cosmologicalConstant) +
            palatiniScalarVelocity
              (regularGeneralMetricC0InverseMetricMatrixAt
                period hPeriod metric 0 point)
              (regularGeneralMetricC0RicciVelocityAt period hPeriod metric
                (regularGeneralMetricC2SmoothDirection
                  period hPeriod metric tensor) point)) ∂measure := by
  rw [regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    regularGeneralMetricC0EinsteinHilbertDensityDerivative_smooth_palatini
      period hPeriod metric couplings tensor point

/-- Gate marker: the true C² EH derivative is Einstein plus its derived
Palatini flux, not an independently supplied residual. -/
theorem regular_general_metric_c2_einstein_hilbert_palatini_density_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      ∫ point,
        (metric.volume point / (2 * couplings.gravitationalCoupling)) *
          (tensorPairing
              (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod
                metric
                (regularGeneralMetricC2SmoothDirection
                  period hPeriod metric tensor) point)
              (einsteinTensorAt
                (regularFrameMetricMatrixMap period hPeriod metric point)
                (regularGeneralMetricC0InverseMetricMatrixAt
                  period hPeriod metric 0 point)
                (regularGeneralMetricC0RicciMatrixAt
                  period hPeriod metric 0 point)
                couplings.cosmologicalConstant) +
            palatiniScalarVelocity
              (regularGeneralMetricC0InverseMetricMatrixAt
                period hPeriod metric 0 point)
              (regularGeneralMetricC0RicciVelocityAt period hPeriod metric
                (regularGeneralMetricC2SmoothDirection
                  period hPeriod metric tensor) point)) ∂measure :=
  regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_palatini
    period hPeriod metric measure couplings tensor

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D
end JanusFormal

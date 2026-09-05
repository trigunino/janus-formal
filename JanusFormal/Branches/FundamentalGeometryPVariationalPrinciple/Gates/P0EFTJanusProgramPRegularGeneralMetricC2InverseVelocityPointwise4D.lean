import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D

/-! # Exact pointwise inverse-metric velocity on the C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

@[reducible] local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

@[reducible] local instance matrix4NormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

@[reducible] local instance matrix4NormedSpace :
    NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4CompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

private def matrix4EntryLinearMap (row column : Fin 4) :
    Matrix4 →ₗ[Real] Real where
  toFun matrix := matrix row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def matrix4EntryCLM (row column : Fin 4) :
    Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap (matrix4EntryLinearMap row column)

/-- Evaluation at one spacetime point of the exact completed inverse-matrix
derivative. -/
def regularGeneralMetricC0PointwiseInverseDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real] Matrix4 :=
  (c2FiniteMatrixValueAtCLM period hPeriod point).comp
    (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
      period hPeriod metric)

theorem regularGeneralMetricC0InverseMetricMatrixAt_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    HasFDerivAt
      (fun variation => regularGeneralMetricC0InverseMetricMatrixAt
        period hPeriod metric variation point)
      (regularGeneralMetricC0PointwiseInverseDerivativeAtZero
        period hPeriod metric point) 0 := by
  have hInner :=
    regularGeneralMetricC2InverseMetricMatrix_hasFDerivAt_zero
      period hPeriod metric
  have hOuter : HasFDerivAt
      (fun matrix : C2Matrix period hPeriod =>
        c2FiniteMatrixValueAtCLM period hPeriod point matrix)
      (c2FiniteMatrixValueAtCLM period hPeriod point)
      (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric 0) :=
    (c2FiniteMatrixValueAtCLM period hPeriod point).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The coefficientwise derivative of Gate479 is exactly the evaluated C²
inverse-matrix derivative of Gate472. -/
theorem regularGeneralMetricC0InverseMetricVelocityAt_eq_pointwiseDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0InverseMetricVelocityAt
        period hPeriod metric direction point =
      regularGeneralMetricC0PointwiseInverseDerivativeAtZero
        period hPeriod metric point direction := by
  ext row column
  let scalarEval :
      C(EffectiveQuotient period hPeriod, Real) →L[Real] Real :=
    ContinuousMap.evalCLM Real point
  let entry := matrix4EntryCLM row column
  have hCoefficient :=
    regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
      period hPeriod metric row column
  have hLeft : HasFDerivAt
      (fun variation =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          variation row column point)
      (scalarEval.comp
        (regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero
          period hPeriod metric row column)) 0 := by
    exact (scalarEval.hasFDerivAt.comp 0 hCoefficient).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hMatrix :=
    regularGeneralMetricC0InverseMetricMatrixAt_hasFDerivAt_zero
      period hPeriod metric point
  have hRight : HasFDerivAt
      (fun variation =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          variation row column point)
      (entry.comp
        (regularGeneralMetricC0PointwiseInverseDerivativeAtZero
          period hPeriod metric point)) 0 := by
    exact (entry.hasFDerivAt.comp 0 hMatrix).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hUnique := hLeft.unique hRight
  have hApply := congrArg (fun derivative => derivative direction) hUnique
  change
    (regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero
      period hPeriod metric row column direction) point =
      regularGeneralMetricC0PointwiseInverseDerivativeAtZero
        period hPeriod metric point direction row column at hApply
  exact hApply

private theorem c2FiniteMatrixValueAt_neg
    (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (-matrix) point =
      -c2FiniteMatrixValueAt period hPeriod 4 matrix point :=
  rfl

private theorem regularFrameMetricInverseC2Matrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularFrameMetricInverseC2Matrix period hPeriod metric) point =
      regularFrameMetricInverseMatrixMap period hPeriod metric point := by
  ext row column
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric row column))
      point = _
  rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

/-- Exact matrix formula in every completed C² direction. -/
theorem regularGeneralMetricC0InverseMetricVelocityAt_eq_relative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0InverseMetricVelocityAt
        period hPeriod metric direction point =
      -(regularGeneralMetricC2RelativeMatrixAt
          period hPeriod metric direction point *
        regularFrameMetricInverseMatrixMap period hPeriod metric point) := by
  rw [regularGeneralMetricC0InverseMetricVelocityAt_eq_pointwiseDerivative]
  unfold regularGeneralMetricC0PointwiseInverseDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply,
    c2FiniteMatrixValueAtCLM_apply,
    regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero_apply,
    c2FiniteMatrixValueAt_neg, c2FiniteMatrixValueAt_product,
    regularFrameMetricInverseC2Matrix_valueAt]
  rfl

/-- On a genuine smooth covariant direction, `δg⁻¹ = -(g⁻¹h)g⁻¹`
pointwise. -/
theorem regularGeneralMetricC0InverseMetricVelocityAt_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      -((regularFrameMetricInverseMatrixMap period hPeriod metric point *
          regularFrameCovariantVariationMatrixAt
            period hPeriod metric tensor point) *
        regularFrameMetricInverseMatrixMap period hPeriod metric point) := by
  rw [regularGeneralMetricC0InverseMetricVelocityAt_eq_relative,
    regularGeneralMetricC2RelativeMatrixAt_smooth]

/-- Gate marker for the exact pointwise inverse-metric velocity. -/
theorem regular_general_metric_c2_inverse_velocity_pointwise_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      -((regularFrameMetricInverseMatrixMap period hPeriod metric point *
          regularFrameCovariantVariationMatrixAt
            period hPeriod metric tensor point) *
        regularFrameMetricInverseMatrixMap period hPeriod metric point) :=
  regularGeneralMetricC0InverseMetricVelocityAt_smooth
    period hPeriod metric tensor point

end
end P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
end JanusFormal

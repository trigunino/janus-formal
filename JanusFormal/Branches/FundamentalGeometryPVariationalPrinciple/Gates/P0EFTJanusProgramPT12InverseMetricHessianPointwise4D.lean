import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeInverseMetricHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D

/-! # Exact pointwise inverse-metric acceleration on the C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12InverseMetricHessianPointwise4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
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

open P0EFTJanusProgramPT12NativeInverseMetricHessian4D
open P0EFTJanusProgramPT12VectorHessianPullback4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D

private theorem nativeInverse_contDiffAt (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffAt Real 2 (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric) 0 :=
  ((regularGeneralMetricC2InverseMetricMatrix_contDiffOn period hPeriod metric).contDiffAt
    ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
      (zero_mem_regularGeneralMetricC2Domain period hPeriod metric))).of_le (by decide)

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

theorem nativeInverseMetric_hessian_pointwise (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    let firstAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric first point
    let secondAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric second point
    fderiv Real (fderiv Real (fun variation => regularGeneralMetricC0InverseMetricMatrixAt
        period hPeriod metric variation point)) 0 first second =
      (secondAt * firstAt + firstAt * secondAt) *
        regularFrameMetricInverseMatrixMap period hPeriod metric point := by
  let evaluation := c2FiniteMatrixValueAtCLM period hPeriod point
  change fderiv Real (fderiv Real (evaluation ∘
    regularGeneralMetricC2InverseMetricMatrix period hPeriod metric)) 0 first second = _
  rw [linearPostHessian evaluation _ 0 first second (nativeInverse_contDiffAt period hPeriod metric),
    nativeInverseMetric_hessian]
  change c2FiniteMatrixValueAtCLM period hPeriod point _ = _
  rw [c2FiniteMatrixValueAtCLM_apply, c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_product, c2FiniteMatrixValueAt_product,
    regularFrameMetricInverseC2Matrix_valueAt]
  rfl

theorem nativeInverseMetric_hessian_smooth (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
    let firstAt := regularFrameCovariantVariationMatrixAt period hPeriod metric first point
    let secondAt := regularFrameCovariantVariationMatrixAt period hPeriod metric second point
    fderiv Real (fderiv Real (fun variation => regularGeneralMetricC0InverseMetricMatrixAt
        period hPeriod metric variation point)) 0
        (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
        (regularGeneralMetricC2SmoothDirection period hPeriod metric second) =
      ((inverse * secondAt) * (inverse * firstAt) +
        (inverse * firstAt) * (inverse * secondAt)) * inverse := by
  simpa only [regularGeneralMetricC2RelativeMatrixAt_smooth] using
    nativeInverseMetric_hessian_pointwise period hPeriod metric
      (regularGeneralMetricC2SmoothDirection period hPeriod metric first)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric second) point

theorem nativeInverseCoefficient_hessian_pointwise
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) (row column : Fin 4) :
    let firstAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric first point
    let secondAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric second point
    fderiv Real (fderiv Real (fun variation => regularGeneralMetricC0InverseMetricCoefficient
        period hPeriod metric variation row column point)) 0 first second =
      ((secondAt * firstAt + firstAt * secondAt) *
        regularFrameMetricInverseMatrixMap period hPeriod metric point) row column := by
  let matrixAt := fun variation => regularGeneralMetricC0InverseMetricMatrixAt
    period hPeriod metric variation point
  have hC2 : ContDiffAt Real 2 matrixAt 0 :=
    (c2FiniteMatrixValueAtCLM period hPeriod point).contDiff.contDiffAt.comp 0
      (nativeInverse_contDiffAt period hPeriod metric)
  change fderiv Real (fderiv Real (matrix4EntryCLM row column ∘ matrixAt)) 0 first second = _
  rw [linearPostHessian _ matrixAt 0 first second hC2]
  exact congrArg (fun matrix : Matrix4 => matrix row column)
    (nativeInverseMetric_hessian_pointwise period hPeriod metric first second point)

end
end P0EFTJanusProgramPT12InverseMetricHessianPointwise4D
end JanusFormal

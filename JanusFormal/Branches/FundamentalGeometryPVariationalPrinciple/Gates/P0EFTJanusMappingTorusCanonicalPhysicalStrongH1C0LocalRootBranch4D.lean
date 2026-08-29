import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D

/-!
# Local matrix-root chart on the canonical strong `C⁰ ∩ H¹` core

The pre-existing continuous pointwise inverse Sylvester family is smooth for
a smooth regular root. Its finitely many scalar coefficients therefore lie in
the canonical strong core and, using the existing strong scalar product,
assemble into a bounded inverse of the strong matrix Sylvester operator.

The inverse-function theorem then gives a genuine open neighborhood of zero
in the full strong tangent Banach space, together with a `C²` local matrix-root
branch. No diagonal specialization, Sobolev embedding, or new physical axiom
is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 100000
noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius RightActions Topology
open MeasureTheory Topology TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev StrongMatrix :=
  P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D.StrongMatrix
    period hPeriod

private abbrev SmoothMatrix :=
  P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D.SmoothMatrix
    period hPeriod

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

local instance canonicalMatrixAddCommGroup : AddCommGroup Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toAddCommGroup

local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace

local instance canonicalMatrixTopologicalSpace : TopologicalSpace Matrix4 :=
  canonicalMatrixUniformSpace.toTopologicalSpace

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

local instance canonicalMatrixModule : Module Real Matrix4 :=
  canonicalMatrixNormedSpace.toModule

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

def coherentSylvesterFamily :
    Matrix4 →L[Real] Matrix4 →L[Real] Matrix4 :=
  ContinuousLinearMap.mul Real Matrix4 +
    (ContinuousLinearMap.mul Real Matrix4).flip

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

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

local instance physicalMeasureFinite :
    MeasureTheory.IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup (StrongScalar period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real (StrongScalar period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace (StrongScalar period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

def smoothMatrixFieldToContinuous
    (root : SmoothQuotientField period hPeriod Matrix4) :
    MatrixField (EffectiveQuotient period hPeriod) where
  toFun := root
  continuous_toFun := root.contMDiff_toFun.continuous

theorem pointwiseSylvesterUnit_contMDiff
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞
      (pointwiseSylvesterUnit
        (smoothMatrixFieldToContinuous period hPeriod root) hRegular) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  change ContMDiff coverModelWithCorners
    (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞
    (fun point =>
      (pointwiseSylvesterUnit
        (smoothMatrixFieldToContinuous period hPeriod root) hRegular point :
          Matrix4 →L[Real] Matrix4))
  simp_rw [pointwiseSylvesterUnit_coe]
  change ContMDiff coverModelWithCorners
    (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞
    (fun point => coherentSylvesterFamily (root point))
  exact coherentSylvesterFamily.contMDiff.comp root.contMDiff_toFun

theorem pointwiseInverseSylvesterField_contMDiff
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞
      (pointwiseInverseSylvesterField
        (smoothMatrixFieldToContinuous period hPeriod root) hRegular) := by
  change ContMDiff coverModelWithCorners
    (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞
    (fun point =>
      ((↑((pointwiseSylvesterUnit
        (smoothMatrixFieldToContinuous period hPeriod root)
          hRegular point)⁻¹)) : Matrix4 →L[Real] Matrix4))
  exact Units.contMDiff_val.comp
    ((contMDiff_inv
      (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞).comp
      (pointwiseSylvesterUnit_contMDiff period hPeriod root hRegular))

/-- Continuous coordinate projection for the canonical matrix norm. -/
def matrixEntryLinearMap (row column : Fin 4) : Matrix4 →ₗ[Real] Real where
  toFun matrix := matrix row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixEntryCLM (row column : Fin 4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap (matrixEntryLinearMap row column)

/-- Standard matrix unit. -/
def matrixUnit (row column : Fin 4) : Matrix4 :=
  Matrix.single row column 1

/-- Smooth scalar coefficients of the inverse Sylvester family. -/
def inverseSylvesterCoefficient
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (outputRow outputColumn inputRow inputColumn : Fin 4) :
    SmoothQuotientField period hPeriod Real where
  toFun point :=
    matrixEntryCLM outputRow outputColumn
      (pointwiseInverseSylvesterField
        (smoothMatrixFieldToContinuous period hPeriod root) hRegular point
        (matrixUnit inputRow inputColumn))
  contMDiff_toFun :=
    (matrixEntryCLM outputRow outputColumn).contMDiff.comp
      ((pointwiseInverseSylvesterField_contMDiff
        period hPeriod root hRegular).clm_apply contMDiff_const)

@[simp]
theorem inverseSylvesterCoefficient_apply
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (outputRow outputColumn inputRow inputColumn : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    inverseSylvesterCoefficient period hPeriod root hRegular
        outputRow outputColumn inputRow inputColumn point =
      pointwiseInverseSylvesterField
        (smoothMatrixFieldToContinuous period hPeriod root) hRegular point
        (matrixUnit inputRow inputColumn) outputRow outputColumn :=
  rfl

/-- Strong lift of one smooth inverse-Sylvester coefficient. -/
def inverseSylvesterCoefficientStrong
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (outputRow outputColumn inputRow inputColumn : Fin 4) :
    StrongScalar period hPeriod :=
  smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
    (inverseSylvesterCoefficient period hPeriod root hRegular
      outputRow outputColumn inputRow inputColumn)

/-- One output coordinate of the inverse Sylvester operator on the strong
core. -/
def strongInverseSylvesterCoordinate
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (outputRow outputColumn : Fin 4) :
    StrongMatrix period hPeriod →L[Real] StrongScalar period hPeriod :=
  ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
    (scalarStrongProduct period hPeriod
      (inverseSylvesterCoefficientStrong period hPeriod root hRegular
        outputRow outputColumn inputRow inputColumn)).comp
      ((ContinuousLinearMap.proj inputColumn :
          (Fin 4 → StrongScalar period hPeriod) →L[Real]
            StrongScalar period hPeriod).comp
        (ContinuousLinearMap.proj inputRow :
          StrongMatrix period hPeriod →L[Real]
            (Fin 4 → StrongScalar period hPeriod)))

/-- The smooth pointwise inverse Sylvester family acts boundedly on the
canonical strong matrix core. -/
def strongInverseSylvesterOperator
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    StrongMatrix period hPeriod →L[Real] StrongMatrix period hPeriod :=
  ContinuousLinearMap.pi fun outputRow : Fin 4 =>
    ContinuousLinearMap.pi fun outputColumn : Fin 4 =>
      strongInverseSylvesterCoordinate period hPeriod root hRegular
        outputRow outputColumn

@[simp]
theorem strongInverseSylvesterOperator_apply
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : StrongMatrix period hPeriod)
    (outputRow outputColumn : Fin 4) :
    strongInverseSylvesterOperator period hPeriod root hRegular variation
        outputRow outputColumn =
      ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
        scalarStrongProduct period hPeriod
          (inverseSylvesterCoefficientStrong period hPeriod root hRegular
            outputRow outputColumn inputRow inputColumn)
          (variation inputRow inputColumn) := by
  simp [strongInverseSylvesterOperator, strongInverseSylvesterCoordinate]

/-- Coordinatewise scalar presentation of a smooth matrix field. -/
def smoothMatrixFieldCoefficients
    (root : SmoothQuotientField period hPeriod Matrix4) :
    SmoothMatrix period hPeriod :=
  fun row column =>
    { toFun := fun point => root point row column
      contMDiff_toFun :=
        (matrixEntryCLM row column).contMDiff.comp root.contMDiff_toFun }

@[simp]
theorem smoothMatrixFieldCoefficients_apply
    (root : SmoothQuotientField period hPeriod Matrix4)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    smoothMatrixFieldCoefficients period hPeriod root row column point =
      root point row column :=
  rfl

/-- A smooth matrix field lifted into the strong matrix core. -/
def smoothMatrixFieldToStrong
    (root : SmoothQuotientField period hPeriod Matrix4) :
    StrongMatrix period hPeriod :=
  smoothMatrixToStrong period hPeriod
    (smoothMatrixFieldCoefficients period hPeriod root)

/-- Smooth coefficient formula for applying the inverse Sylvester family. -/
def smoothInverseSylvesterApply
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : SmoothMatrix period hPeriod) :
    SmoothMatrix period hPeriod :=
  fun outputRow outputColumn =>
    ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
      smoothScalarFieldMul period hPeriod
        (inverseSylvesterCoefficient period hPeriod root hRegular
          outputRow outputColumn inputRow inputColumn)
        (variation inputRow inputColumn)

@[simp]
theorem smoothScalarField_sum_apply
    {Index : Type*} (indices : Finset Index)
    (fields : Index → SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    (Finset.sum indices fields) point =
      Finset.sum indices (fun index => fields index point) := by
  let evaluation : SmoothQuotientField period hPeriod Real →+ Real :=
    { toFun := fun field => field point
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum evaluation fields indices

/-- The strong inverse formula agrees exactly with its smooth coefficient
formula on the dense smooth core. -/
theorem strongInverseSylvesterOperator_smooth
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : SmoothMatrix period hPeriod) :
    strongInverseSylvesterOperator period hPeriod root hRegular
        (smoothMatrixToStrong period hPeriod variation) =
      smoothMatrixToStrong period hPeriod
        (smoothInverseSylvesterApply period hPeriod root hRegular
          variation) := by
  funext outputRow outputColumn
  rw [strongInverseSylvesterOperator_apply]
  change (∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
      scalarStrongProduct period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (inverseSylvesterCoefficient period hPeriod root hRegular
            outputRow outputColumn inputRow inputColumn))
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (variation inputRow inputColumn))) =
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
      (smoothInverseSylvesterApply period hPeriod root hRegular variation
        outputRow outputColumn)
  rw [show smoothInverseSylvesterApply period hPeriod root hRegular variation
      outputRow outputColumn =
      ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
        smoothScalarFieldMul period hPeriod
          (inverseSylvesterCoefficient period hPeriod root hRegular
            outputRow outputColumn inputRow inputColumn)
          (variation inputRow inputColumn) from rfl]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputRow _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputColumn _
  exact canonicalPhysicalScalarStrongH1C0CoreProduct_smooth
    period hPeriod
      (inverseSylvesterCoefficient period hPeriod root hRegular
        outputRow outputColumn inputRow inputColumn)
      (variation inputRow inputColumn)

/-- Value of a coordinatewise smooth matrix at one point. -/
def smoothMatrixValue
    (variation : SmoothMatrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  fun row column => variation row column point

theorem matrix_eq_sum_units (matrix : Matrix4) :
    (∑ row : Fin 4, ∑ column : Fin 4,
      matrix row column • matrixUnit row column) = matrix := by
  simpa [matrixUnit] using (Matrix.matrix_eq_sum_single matrix).symm

/-- Coordinate expansion of the pointwise inverse family. -/
theorem inverseSylvesterCoefficient_expansion
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (point : EffectiveQuotient period hPeriod)
    (variation : Matrix4) (outputRow outputColumn : Fin 4) :
    (∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
      inverseSylvesterCoefficient period hPeriod root hRegular
          outputRow outputColumn inputRow inputColumn point *
        variation inputRow inputColumn) =
      pointwiseInverseSylvesterField
          (smoothMatrixFieldToContinuous period hPeriod root) hRegular point
          variation outputRow outputColumn := by
  let inverse := pointwiseInverseSylvesterField
    (smoothMatrixFieldToContinuous period hPeriod root) hRegular point
  have hExpansion :
      inverse variation =
        ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
          variation inputRow inputColumn •
            inverse (matrixUnit inputRow inputColumn) := by
    calc
      inverse variation = inverse
          (∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
            variation inputRow inputColumn •
              matrixUnit inputRow inputColumn) := by
        rw [matrix_eq_sum_units]
      _ = ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
          inverse (variation inputRow inputColumn •
            matrixUnit inputRow inputColumn) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro inputRow _
        rw [map_sum]
      _ = ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
          variation inputRow inputColumn •
            inverse (matrixUnit inputRow inputColumn) := by
        apply Finset.sum_congr rfl
        intro inputRow _
        apply Finset.sum_congr rfl
        intro inputColumn _
        exact inverse.map_smul _ _
  have hEntry := congrArg (fun matrix : Matrix4 =>
    matrix outputRow outputColumn) hExpansion
  simpa [inverse, inverseSylvesterCoefficient_apply, Matrix.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using hEntry.symm

/-- Smooth Sylvester action in scalar matrix coordinates. -/
def smoothMatrixSylvester
    (root variation : SmoothMatrix period hPeriod) :
    SmoothMatrix period hPeriod :=
  smoothMatrixProduct period hPeriod root variation +
    smoothMatrixProduct period hPeriod variation root

theorem smoothMatrixSylvester_value
    (root : SmoothQuotientField period hPeriod Matrix4)
    (variation : SmoothMatrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothMatrixValue period hPeriod
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) variation)
        point =
      canonicalSylvesterOperator (root point)
        (smoothMatrixValue period hPeriod variation point) := by
  ext row column
  simp [smoothMatrixValue, smoothMatrixSylvester, smoothMatrixProduct,
    smoothScalarFieldMul, smoothScalarField_sum_apply,
    canonicalSylvesterOperator_apply, Matrix.mul_apply]

/-- Left pointwise inverse identity expressed on smooth coordinates. -/
theorem smoothInverseSylvesterApply_left
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : SmoothMatrix period hPeriod) :
    smoothInverseSylvesterApply period hPeriod root hRegular
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) variation) =
      variation := by
  funext outputRow outputColumn
  apply SmoothQuotientField.ext
  intro point
  change (∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
      inverseSylvesterCoefficient period hPeriod root hRegular
          outputRow outputColumn inputRow inputColumn point *
        smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) variation
            inputRow inputColumn point) =
      variation outputRow outputColumn point
  rw [inverseSylvesterCoefficient_expansion]
  rw [show (fun inputRow inputColumn =>
      smoothMatrixSylvester period hPeriod
        (smoothMatrixFieldCoefficients period hPeriod root) variation
          inputRow inputColumn point) =
      canonicalSylvesterOperator (root point)
        (smoothMatrixValue period hPeriod variation point) from
    smoothMatrixSylvester_value period hPeriod root variation point]
  exact congrArg (fun matrix : Matrix4 => matrix outputRow outputColumn)
    (pointwiseInverseSylvesterField_left
      (smoothMatrixFieldToContinuous period hPeriod root) hRegular point
      (smoothMatrixValue period hPeriod variation point))

/-- Right pointwise inverse identity expressed on smooth coordinates. -/
theorem smoothInverseSylvesterApply_right
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : SmoothMatrix period hPeriod) :
    smoothMatrixSylvester period hPeriod
        (smoothMatrixFieldCoefficients period hPeriod root)
        (smoothInverseSylvesterApply period hPeriod root hRegular variation) =
      variation := by
  funext outputRow outputColumn
  apply SmoothQuotientField.ext
  intro point
  have hInverseValue :
      smoothMatrixValue period hPeriod
          (smoothInverseSylvesterApply period hPeriod root hRegular variation)
          point =
        pointwiseInverseSylvesterField
          (smoothMatrixFieldToContinuous period hPeriod root) hRegular point
          (smoothMatrixValue period hPeriod variation point) := by
    ext row column
    simpa [smoothMatrixValue, smoothInverseSylvesterApply,
      smoothScalarFieldMul, smoothScalarField_sum_apply] using
        (inverseSylvesterCoefficient_expansion period hPeriod root hRegular
          point (smoothMatrixValue period hPeriod variation point) row column)
  have hValue := smoothMatrixSylvester_value period hPeriod root
    (smoothInverseSylvesterApply period hPeriod root hRegular variation) point
  rw [hInverseValue] at hValue
  have hRight := pointwiseInverseSylvesterField_right
    (smoothMatrixFieldToContinuous period hPeriod root) hRegular point
    (smoothMatrixValue period hPeriod variation point)
  exact congrArg (fun matrix : Matrix4 => matrix outputRow outputColumn)
    (hValue.trans hRight)

/-- Coordinatewise smooth matrices are dense in the finite strong matrix
core. -/
theorem smoothMatrixToStrong_denseRange :
    DenseRange (smoothMatrixToStrong period hPeriod) := by
  exact DenseRange.piMap fun _ : Fin 4 =>
    DenseRange.piMap fun _ : Fin 4 =>
      smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
        period hPeriod

/-- The strong Sylvester action agrees with the smooth pointwise action on
the dense smooth core. -/
theorem strongMatrixSylvester_smooth
    (root : SmoothQuotientField period hPeriod Matrix4)
    (variation : SmoothMatrix period hPeriod) :
    strongMatrixSylvester period hPeriod
        (smoothMatrixFieldToStrong period hPeriod root)
        (smoothMatrixToStrong period hPeriod variation) =
      smoothMatrixToStrong period hPeriod
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) variation) := by
  change strongMatrixProduct period hPeriod
          (smoothMatrixToStrong period hPeriod
            (smoothMatrixFieldCoefficients period hPeriod root))
          (smoothMatrixToStrong period hPeriod variation) +
        strongMatrixProduct period hPeriod
          (smoothMatrixToStrong period hPeriod variation)
          (smoothMatrixToStrong period hPeriod
            (smoothMatrixFieldCoefficients period hPeriod root)) = _
  rw [strongMatrixProduct_smooth, strongMatrixProduct_smooth]
  rw [smoothMatrixSylvester]
  exact (smoothMatrixToStrong period hPeriod).map_add _ _ |>.symm

/-- The coefficientwise strong inverse is a left inverse of the strong
Sylvester operator. -/
theorem strongInverseSylvesterOperator_left
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : StrongMatrix period hPeriod) :
    strongInverseSylvesterOperator period hPeriod root hRegular
        (strongMatrixSylvester period hPeriod
          (smoothMatrixFieldToStrong period hPeriod root) variation) =
      variation := by
  let inverse := strongInverseSylvesterOperator period hPeriod root hRegular
  let sylvester := strongMatrixSylvester period hPeriod
    (smoothMatrixFieldToStrong period hPeriod root)
  refine DenseRange.induction_on
    (smoothMatrixToStrong_denseRange period hPeriod) variation
    (isClosed_eq (inverse.comp sylvester).continuous
      (ContinuousLinearMap.id Real
        (StrongMatrix period hPeriod)).continuous) ?_
  intro smooth
  change inverse (sylvester
      (smoothMatrixToStrong period hPeriod smooth)) =
    smoothMatrixToStrong period hPeriod smooth
  rw [show sylvester (smoothMatrixToStrong period hPeriod smooth) =
      smoothMatrixToStrong period hPeriod
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) smooth) from
    strongMatrixSylvester_smooth period hPeriod root smooth]
  rw [show inverse
      (smoothMatrixToStrong period hPeriod
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) smooth)) =
      smoothMatrixToStrong period hPeriod
        (smoothInverseSylvesterApply period hPeriod root hRegular
          (smoothMatrixSylvester period hPeriod
            (smoothMatrixFieldCoefficients period hPeriod root) smooth)) from
    strongInverseSylvesterOperator_smooth period hPeriod root hRegular _]
  rw [smoothInverseSylvesterApply_left]

/-- The coefficientwise strong inverse is a right inverse of the strong
Sylvester operator. -/
theorem strongInverseSylvesterOperator_right
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : StrongMatrix period hPeriod) :
    strongMatrixSylvester period hPeriod
        (smoothMatrixFieldToStrong period hPeriod root)
        (strongInverseSylvesterOperator period hPeriod root hRegular
          variation) =
      variation := by
  let inverse := strongInverseSylvesterOperator period hPeriod root hRegular
  let sylvester := strongMatrixSylvester period hPeriod
    (smoothMatrixFieldToStrong period hPeriod root)
  refine DenseRange.induction_on
    (smoothMatrixToStrong_denseRange period hPeriod) variation
    (isClosed_eq (sylvester.comp inverse).continuous
      (ContinuousLinearMap.id Real
        (StrongMatrix period hPeriod)).continuous) ?_
  intro smooth
  change sylvester (inverse
      (smoothMatrixToStrong period hPeriod smooth)) =
    smoothMatrixToStrong period hPeriod smooth
  rw [show inverse (smoothMatrixToStrong period hPeriod smooth) =
      smoothMatrixToStrong period hPeriod
        (smoothInverseSylvesterApply period hPeriod root hRegular smooth) from
    strongInverseSylvesterOperator_smooth period hPeriod root hRegular smooth]
  rw [show sylvester
      (smoothMatrixToStrong period hPeriod
        (smoothInverseSylvesterApply period hPeriod root hRegular smooth)) =
      smoothMatrixToStrong period hPeriod
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root)
          (smoothInverseSylvesterApply period hPeriod root hRegular smooth)) from
    strongMatrixSylvester_smooth period hPeriod root _]
  rw [smoothInverseSylvesterApply_right]

/-- Genuine bounded Sylvester equivalence on the strong matrix core, derived
from smooth pointwise regularity. -/
def strongMatrixSylvesterEquiv
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    StrongMatrix period hPeriod ≃L[Real] StrongMatrix period hPeriod where
  toFun := strongMatrixSylvester period hPeriod
    (smoothMatrixFieldToStrong period hPeriod root)
  invFun := strongInverseSylvesterOperator period hPeriod root hRegular
  left_inv := strongInverseSylvesterOperator_left period hPeriod root hRegular
  right_inv := strongInverseSylvesterOperator_right period hPeriod root hRegular
  map_add' first second := by simp
  map_smul' scalar variation := by simp
  continuous_toFun := (strongMatrixSylvester period hPeriod
    (smoothMatrixFieldToStrong period hPeriod root)).continuous
  continuous_invFun :=
    (strongInverseSylvesterOperator period hPeriod root hRegular).continuous

theorem strongMatrixSylvesterEquiv_forward_eq
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    (strongMatrixSylvesterEquiv period hPeriod root hRegular :
      StrongMatrix period hPeriod →L[Real] StrongMatrix period hPeriod) =
      strongMatrixSylvester period hPeriod
        (smoothMatrixFieldToStrong period hPeriod root) :=
  rfl

/-- Sylvester derivative as a continuous family over the strong matrix
space. -/
def strongMatrixSylvesterFamily :
    StrongMatrix period hPeriod →L[Real]
      StrongMatrix period hPeriod →L[Real] StrongMatrix period hPeriod :=
  strongMatrixProduct period hPeriod +
    (strongMatrixProduct period hPeriod).flip

@[simp]
theorem strongMatrixSylvesterFamily_apply
    (root : StrongMatrix period hPeriod) :
    strongMatrixSylvesterFamily period hPeriod root =
      strongMatrixSylvester period hPeriod root :=
  rfl

theorem strongMatrixSquare_contDiff_two :
    ContDiff Real 2 (strongMatrixSquare period hPeriod) :=
  (strongMatrixSquare_contDiff period hPeriod).of_le (by norm_num)

/-- Open strong-field locus on which the Sylvester derivative is represented
by a bounded linear equivalence. -/
def strongMatrixSylvesterRegularRootSet :
    Set (StrongMatrix period hPeriod) :=
  strongMatrixSylvesterFamily period hPeriod ⁻¹'
    Set.range ((↑) :
      (StrongMatrix period hPeriod ≃L[Real]
        StrongMatrix period hPeriod) →
      StrongMatrix period hPeriod →L[Real]
        StrongMatrix period hPeriod)

theorem strongMatrixSylvesterRegularRootSet_isOpen :
    IsOpen (strongMatrixSylvesterRegularRootSet period hPeriod) := by
  apply ContinuousLinearEquiv.isOpen.preimage
  exact (strongMatrixSylvesterFamily period hPeriod).continuous

theorem smoothMatrixFieldToStrong_mem_sylvesterRegularRootSet
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    smoothMatrixFieldToStrong period hPeriod root ∈
      strongMatrixSylvesterRegularRootSet period hPeriod := by
  exact ⟨strongMatrixSylvesterEquiv period hPeriod root hRegular,
    strongMatrixSylvesterEquiv_forward_eq period hPeriod root hRegular⟩

/-- Base inverse-function chart for squaring on the complete strong core. -/
def strongMatrixC2BaseSquareChart
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    OpenPartialHomeomorph (StrongMatrix period hPeriod)
      (StrongMatrix period hPeriod) :=
  (strongMatrixSquare_contDiff_two period hPeriod).contDiffAt
    |>.toOpenPartialHomeomorph
      (strongMatrixSquare period hPeriod)
      ((strongMatrixSquare_hasFDerivAt period hPeriod
        (smoothMatrixFieldToStrong period hPeriod root)).congr_fderiv
          (strongMatrixSylvesterEquiv_forward_eq
            period hPeriod root hRegular).symm)
      (by norm_num)

/-- Restriction to the open locus where every encountered derivative is a
bounded equivalence. -/
def strongMatrixC2LocalSquareChart
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    OpenPartialHomeomorph (StrongMatrix period hPeriod)
      (StrongMatrix period hPeriod) :=
  (strongMatrixC2BaseSquareChart period hPeriod root hRegular).restrOpen
    (strongMatrixSylvesterRegularRootSet period hPeriod)
    (strongMatrixSylvesterRegularRootSet_isOpen period hPeriod)

def strongMatrixC2LocalRootTarget
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    Set (StrongMatrix period hPeriod) :=
  (strongMatrixC2LocalSquareChart period hPeriod root hRegular).target

theorem strongMatrixC2LocalRootTarget_isOpen
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (strongMatrixC2LocalRootTarget period hPeriod root hRegular) :=
  (strongMatrixC2LocalSquareChart period hPeriod root hRegular).open_target

theorem smoothMatrixFieldToStrong_mem_localSquareChart_source
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    smoothMatrixFieldToStrong period hPeriod root ∈
      (strongMatrixC2LocalSquareChart period hPeriod root hRegular).source := by
  rw [strongMatrixC2LocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨(strongMatrixSquare_contDiff_two period hPeriod).contDiffAt
      |>.mem_toOpenPartialHomeomorph_source
        ((strongMatrixSquare_hasFDerivAt period hPeriod
          (smoothMatrixFieldToStrong period hPeriod root)).congr_fderiv
            (strongMatrixSylvesterEquiv_forward_eq
              period hPeriod root hRegular).symm)
        (by norm_num),
    smoothMatrixFieldToStrong_mem_sylvesterRegularRootSet
      period hPeriod root hRegular⟩

theorem smoothMatrixFieldSquare_mem_localRootTarget
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    strongMatrixSquare period hPeriod
        (smoothMatrixFieldToStrong period hPeriod root) ∈
      strongMatrixC2LocalRootTarget period hPeriod root hRegular := by
  exact (strongMatrixC2LocalSquareChart period hPeriod root hRegular).map_source
    (smoothMatrixFieldToStrong_mem_localSquareChart_source
      period hPeriod root hRegular)

/-- Local `C²` root branch on the strong matrix core. -/
def strongMatrixC2LocalRootBranch
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    StrongMatrix period hPeriod → StrongMatrix period hPeriod :=
  (strongMatrixC2LocalSquareChart period hPeriod root hRegular).symm

theorem strongMatrixC2LocalRootBranch_square
    {root : SmoothQuotientField period hPeriod Matrix4}
    {hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))}
    {nearby : StrongMatrix period hPeriod}
    (hNearby : nearby ∈
      strongMatrixC2LocalRootTarget period hPeriod root hRegular) :
    strongMatrixSquare period hPeriod
        (strongMatrixC2LocalRootBranch period hPeriod root hRegular nearby) =
      nearby := by
  exact (strongMatrixC2LocalSquareChart period hPeriod root hRegular).right_inv
    hNearby

theorem strongMatrixC2LocalRootBranch_at_center
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    strongMatrixC2LocalRootBranch period hPeriod root hRegular
        (strongMatrixSquare period hPeriod
          (smoothMatrixFieldToStrong period hPeriod root)) =
      smoothMatrixFieldToStrong period hPeriod root := by
  exact (strongMatrixC2LocalSquareChart period hPeriod root hRegular).left_inv
    (smoothMatrixFieldToStrong_mem_localSquareChart_source
      period hPeriod root hRegular)

theorem strongMatrixC2LocalRootBranch_contDiffAt
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : StrongMatrix period hPeriod)
    (hNearby : nearby ∈
      strongMatrixC2LocalRootTarget period hPeriod root hRegular) :
    ContDiffAt Real 2
      (strongMatrixC2LocalRootBranch period hPeriod root hRegular) nearby := by
  have hSource :=
    (strongMatrixC2LocalSquareChart period hPeriod root hRegular).map_target
      hNearby
  rw [strongMatrixC2LocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  rcases hSource.2 with ⟨equiv, hEquiv⟩
  apply (strongMatrixC2LocalSquareChart period hPeriod root hRegular)
    |>.contDiffAt_symm hNearby (f₀' := equiv)
  · exact (strongMatrixSquare_hasFDerivAt period hPeriod
      ((strongMatrixC2LocalSquareChart period hPeriod root hRegular).symm
        nearby)).congr_fderiv hEquiv.symm
  · exact (strongMatrixSquare_contDiff_two period hPeriod).contDiffAt

theorem strongMatrixC2LocalRootBranch_contDiffOn
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContDiffOn Real 2
      (strongMatrixC2LocalRootBranch period hPeriod root hRegular)
      (strongMatrixC2LocalRootTarget period hPeriod root hRegular) := by
  intro nearby hNearby
  exact (strongMatrixC2LocalRootBranch_contDiffAt period hPeriod
    root hRegular nearby hNearby).contDiffWithinAt

/-- Zero-centered open perturbation domain in the full tangent Banach space. -/
def strongMatrixRootPerturbationDomain
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    Set (StrongMatrix period hPeriod) :=
  (fun variation =>
    strongMatrixSquare period hPeriod
      (smoothMatrixFieldToStrong period hPeriod root) + variation) ⁻¹'
    strongMatrixC2LocalRootTarget period hPeriod root hRegular

theorem strongMatrixRootPerturbationDomain_isOpen
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (strongMatrixRootPerturbationDomain
      period hPeriod root hRegular) := by
  exact (strongMatrixC2LocalRootTarget_isOpen period hPeriod root hRegular)
    |>.preimage (continuous_const.add continuous_id)

theorem zero_mem_strongMatrixRootPerturbationDomain
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    (0 : StrongMatrix period hPeriod) ∈
      strongMatrixRootPerturbationDomain period hPeriod root hRegular := by
  simpa [strongMatrixRootPerturbationDomain] using
    smoothMatrixFieldSquare_mem_localRootTarget
      period hPeriod root hRegular

def strongMatrixRootPerturbationBranch
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    StrongMatrix period hPeriod → StrongMatrix period hPeriod :=
  fun variation => strongMatrixC2LocalRootBranch period hPeriod root hRegular
    (strongMatrixSquare period hPeriod
      (smoothMatrixFieldToStrong period hPeriod root) + variation)

theorem strongMatrixRootPerturbationBranch_square
    {root : SmoothQuotientField period hPeriod Matrix4}
    {hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))}
    {variation : StrongMatrix period hPeriod}
    (hVariation : variation ∈
      strongMatrixRootPerturbationDomain period hPeriod root hRegular) :
    strongMatrixSquare period hPeriod
        (strongMatrixRootPerturbationBranch
          period hPeriod root hRegular variation) =
      strongMatrixSquare period hPeriod
          (smoothMatrixFieldToStrong period hPeriod root) + variation :=
  strongMatrixC2LocalRootBranch_square period hPeriod hVariation

theorem strongMatrixRootPerturbationBranch_contDiffOn
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContDiffOn Real 2
      (strongMatrixRootPerturbationBranch period hPeriod root hRegular)
      (strongMatrixRootPerturbationDomain period hPeriod root hRegular) := by
  intro variation hVariation
  have hOuter := strongMatrixC2LocalRootBranch_contDiffAt period hPeriod
    root hRegular
      (strongMatrixSquare period hPeriod
        (smoothMatrixFieldToStrong period hPeriod root) + variation)
      hVariation
  have hInner : ContDiffAt Real 2
      (fun current : StrongMatrix period hPeriod =>
        strongMatrixSquare period hPeriod
          (smoothMatrixFieldToStrong period hPeriod root) + current)
      variation :=
    contDiffAt_const.add contDiffAt_id
  rw [show strongMatrixRootPerturbationBranch
      period hPeriod root hRegular =
      strongMatrixC2LocalRootBranch period hPeriod root hRegular ∘
        (fun current : StrongMatrix period hPeriod =>
          strongMatrixSquare period hPeriod
            (smoothMatrixFieldToStrong period hPeriod root) + current) by rfl]
  exact (hOuter.comp variation hInner).contDiffWithinAt

/-- Complete strong local-root certificate on a genuine open neighborhood of
zero in the full tangent Banach space. -/
theorem canonical_physical_strong_h1_c0_local_root_gate
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (strongMatrixRootPerturbationDomain
      period hPeriod root hRegular) ∧
      (0 : StrongMatrix period hPeriod) ∈
        strongMatrixRootPerturbationDomain period hPeriod root hRegular ∧
      ContDiffOn Real 2
        (strongMatrixRootPerturbationBranch period hPeriod root hRegular)
        (strongMatrixRootPerturbationDomain period hPeriod root hRegular) ∧
      ∀ variation,
        variation ∈ strongMatrixRootPerturbationDomain
            period hPeriod root hRegular →
          strongMatrixSquare period hPeriod
              (strongMatrixRootPerturbationBranch
                period hPeriod root hRegular variation) =
            strongMatrixSquare period hPeriod
                (smoothMatrixFieldToStrong period hPeriod root) + variation := by
  exact ⟨strongMatrixRootPerturbationDomain_isOpen
      period hPeriod root hRegular,
    zero_mem_strongMatrixRootPerturbationDomain
      period hPeriod root hRegular,
    strongMatrixRootPerturbationBranch_contDiffOn
      period hPeriod root hRegular,
    fun _ hVariation =>
      strongMatrixRootPerturbationBranch_square period hPeriod hVariation⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
end JanusFormal

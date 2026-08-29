import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D

/-!
# Smooth finite-matrix operator families on the canonical strong core

Every smooth family of operators on finite real matrices acts boundedly on
the canonical strong `C⁰ ∩ H¹` matrix core. If the family is pointwise
bijective, its smooth pointwise inverse lifts as well and gives a bounded
linear equivalence of the strong core.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev MatrixN (dimension : Nat) :=
  Matrix (Fin dimension) (Fin dimension) Real

@[reducible] local instance finiteMatrixNormedAddCommGroup (dimension : Nat) :
    NormedAddCommGroup (MatrixN dimension) :=
  Matrix.normedAddCommGroup

@[reducible] local instance finiteMatrixNormedSpace (dimension : Nat) :
    NormedSpace Real (MatrixN dimension) :=
  Matrix.normedSpace

local instance finiteMatrixOperatorNormedAddCommGroup (dimension : Nat) :
    NormedAddCommGroup (MatrixN dimension →L[Real] MatrixN dimension) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance finiteMatrixOperatorNormedSpace (dimension : Nat) :
    NormedSpace Real (MatrixN dimension →L[Real] MatrixN dimension) :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

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
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
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

/-- A pointwise bijective finite-matrix operator as a continuous linear
equivalence. -/
def pointwiseFiniteMatrixOperatorEquiv
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (point : EffectiveQuotient period hPeriod) :
    MatrixN dimension ≃L[Real] MatrixN dimension :=
  (LinearEquiv.ofBijective
    (operator point).toLinearMap (hRegular point)).toContinuousLinearEquiv

theorem pointwiseFiniteMatrixOperator_isInvertible
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (point : EffectiveQuotient period hPeriod) :
    (operator point).IsInvertible := by
  exact ⟨pointwiseFiniteMatrixOperatorEquiv
    period hPeriod dimension operator hRegular point, rfl⟩

/-- Smooth family of pointwise inverse operators. -/
def pointwiseFiniteMatrixInverseField
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point)) :
    SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension) where
  toFun point := (operator point).inverse
  contMDiff_toFun := by
    intro point
    exact
      (pointwiseFiniteMatrixOperator_isInvertible
          period hPeriod dimension operator hRegular point
        |>.contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt
        (operator.contMDiff_toFun point)

theorem pointwiseFiniteMatrixInverseField_left
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (point : EffectiveQuotient period hPeriod)
    (matrix : MatrixN dimension) :
    pointwiseFiniteMatrixInverseField
        period hPeriod dimension operator hRegular point
        (operator point matrix) = matrix := by
  change (operator point).inverse (operator point matrix) = matrix
  rw [show (operator point).inverse =
      (pointwiseFiniteMatrixOperatorEquiv
        period hPeriod dimension operator hRegular point).symm.toContinuousLinearMap by
    exact ContinuousLinearMap.inverse_equiv
      (pointwiseFiniteMatrixOperatorEquiv
        period hPeriod dimension operator hRegular point)]
  exact (pointwiseFiniteMatrixOperatorEquiv
    period hPeriod dimension operator hRegular point).symm_apply_apply matrix

theorem pointwiseFiniteMatrixInverseField_right
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (point : EffectiveQuotient period hPeriod)
    (matrix : MatrixN dimension) :
    operator point
        (pointwiseFiniteMatrixInverseField
          period hPeriod dimension operator hRegular point matrix) = matrix := by
  change operator point ((operator point).inverse matrix) = matrix
  rw [show (operator point).inverse =
      (pointwiseFiniteMatrixOperatorEquiv
        period hPeriod dimension operator hRegular point).symm.toContinuousLinearMap by
    exact ContinuousLinearMap.inverse_equiv
      (pointwiseFiniteMatrixOperatorEquiv
        period hPeriod dimension operator hRegular point)]
  exact (pointwiseFiniteMatrixOperatorEquiv
    period hPeriod dimension operator hRegular point).apply_symm_apply matrix

/-- Continuous projection onto one matrix entry. -/
def finiteMatrixEntryLinearMap
    (dimension : Nat) (row column : Fin dimension) :
    MatrixN dimension →ₗ[Real] Real where
  toFun matrix := matrix row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteMatrixEntryCLM
    (dimension : Nat) (row column : Fin dimension) :
    MatrixN dimension →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    (finiteMatrixEntryLinearMap dimension row column)

/-- Standard matrix unit. -/
def finiteMatrixUnit
    (dimension : Nat) (row column : Fin dimension) : MatrixN dimension :=
  Matrix.single row column 1

/-- Smooth scalar coefficients of a finite-matrix operator family. -/
def finiteMatrixOperatorCoefficient
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (outputRow outputColumn inputRow inputColumn : Fin dimension) :
    SmoothQuotientField period hPeriod Real where
  toFun point :=
    finiteMatrixEntryCLM dimension outputRow outputColumn
      (operator point (finiteMatrixUnit dimension inputRow inputColumn))
  contMDiff_toFun :=
    (finiteMatrixEntryCLM dimension outputRow outputColumn).contMDiff.comp
      (operator.contMDiff_toFun.clm_apply contMDiff_const)

@[simp]
theorem finiteMatrixOperatorCoefficient_apply
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (outputRow outputColumn inputRow inputColumn : Fin dimension)
    (point : EffectiveQuotient period hPeriod) :
    finiteMatrixOperatorCoefficient period hPeriod dimension operator
        outputRow outputColumn inputRow inputColumn point =
      operator point (finiteMatrixUnit dimension inputRow inputColumn)
        outputRow outputColumn :=
  rfl

def finiteMatrixOperatorCoefficientStrong
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (outputRow outputColumn inputRow inputColumn : Fin dimension) :
    StrongScalar period hPeriod :=
  smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
    (finiteMatrixOperatorCoefficient period hPeriod dimension operator
      outputRow outputColumn inputRow inputColumn)

def strongFiniteMatrixOperatorCoordinate
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (outputRow outputColumn : Fin dimension) :
    StrongFiniteMatrix period hPeriod dimension →L[Real]
      StrongScalar period hPeriod :=
  ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
    (scalarStrongProduct period hPeriod
      (finiteMatrixOperatorCoefficientStrong period hPeriod dimension operator
        outputRow outputColumn inputRow inputColumn)).comp
      ((ContinuousLinearMap.proj inputColumn :
          (Fin dimension → StrongScalar period hPeriod) →L[Real]
            StrongScalar period hPeriod).comp
        (ContinuousLinearMap.proj inputRow :
          StrongFiniteMatrix period hPeriod dimension →L[Real]
            (Fin dimension → StrongScalar period hPeriod)))

/-- Bounded strong lift of a smooth finite-matrix operator family. -/
def strongFiniteMatrixOperator
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension)) :
    StrongFiniteMatrix period hPeriod dimension →L[Real]
      StrongFiniteMatrix period hPeriod dimension :=
  ContinuousLinearMap.pi fun outputRow : Fin dimension =>
    ContinuousLinearMap.pi fun outputColumn : Fin dimension =>
      strongFiniteMatrixOperatorCoordinate
        period hPeriod dimension operator outputRow outputColumn

@[simp]
theorem strongFiniteMatrixOperator_apply
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (variation : StrongFiniteMatrix period hPeriod dimension)
    (outputRow outputColumn : Fin dimension) :
    strongFiniteMatrixOperator period hPeriod dimension operator variation
        outputRow outputColumn =
      ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
        scalarStrongProduct period hPeriod
          (finiteMatrixOperatorCoefficientStrong
            period hPeriod dimension operator
              outputRow outputColumn inputRow inputColumn)
          (variation inputRow inputColumn) := by
  simp [strongFiniteMatrixOperator, strongFiniteMatrixOperatorCoordinate]

/-- Coordinatewise action on the dense smooth finite-matrix core. -/
def smoothFiniteMatrixOperatorApply
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (variation : SmoothFiniteMatrix period hPeriod dimension) :
    SmoothFiniteMatrix period hPeriod dimension :=
  fun outputRow outputColumn =>
    ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
      smoothScalarFieldMul period hPeriod
        (finiteMatrixOperatorCoefficient period hPeriod dimension operator
          outputRow outputColumn inputRow inputColumn)
        (variation inputRow inputColumn)

theorem strongFiniteMatrixOperator_smooth
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (variation : SmoothFiniteMatrix period hPeriod dimension) :
    strongFiniteMatrixOperator period hPeriod dimension operator
        (smoothFiniteMatrixToStrong period hPeriod dimension variation) =
      smoothFiniteMatrixToStrong period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension operator variation) := by
  funext outputRow outputColumn
  rw [strongFiniteMatrixOperator_apply]
  change (∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
      scalarStrongProduct period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (finiteMatrixOperatorCoefficient period hPeriod dimension operator
            outputRow outputColumn inputRow inputColumn))
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (variation inputRow inputColumn))) =
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
      (smoothFiniteMatrixOperatorApply period hPeriod dimension operator variation
        outputRow outputColumn)
  rw [show smoothFiniteMatrixOperatorApply
      period hPeriod dimension operator variation outputRow outputColumn =
      ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
        smoothScalarFieldMul period hPeriod
          (finiteMatrixOperatorCoefficient period hPeriod dimension operator
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
      (finiteMatrixOperatorCoefficient period hPeriod dimension operator
        outputRow outputColumn inputRow inputColumn)
      (variation inputRow inputColumn)

/-- Value of a coordinatewise smooth finite matrix at one point. -/
def smoothFiniteMatrixValue
    (dimension : Nat)
    (variation : SmoothFiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) : MatrixN dimension :=
  fun row column => variation row column point

theorem finiteMatrix_eq_sum_units
    (dimension : Nat) (matrix : MatrixN dimension) :
    (∑ row : Fin dimension, ∑ column : Fin dimension,
      matrix row column • finiteMatrixUnit dimension row column) = matrix := by
  simpa [finiteMatrixUnit] using (Matrix.matrix_eq_sum_single matrix).symm

/-- Coordinate expansion of a pointwise operator family. -/
theorem finiteMatrixOperatorCoefficient_expansion
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (point : EffectiveQuotient period hPeriod)
    (variation : MatrixN dimension)
    (outputRow outputColumn : Fin dimension) :
    (∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
      finiteMatrixOperatorCoefficient period hPeriod dimension operator
          outputRow outputColumn inputRow inputColumn point *
        variation inputRow inputColumn) =
      operator point variation outputRow outputColumn := by
  have hExpansion :
      operator point variation =
        ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
          variation inputRow inputColumn •
            operator point (finiteMatrixUnit dimension inputRow inputColumn) := by
    calc
      operator point variation = operator point
          (∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
            variation inputRow inputColumn •
              finiteMatrixUnit dimension inputRow inputColumn) := by
        rw [finiteMatrix_eq_sum_units]
      _ = ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
          operator point (variation inputRow inputColumn •
            finiteMatrixUnit dimension inputRow inputColumn) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro inputRow _
        rw [map_sum]
      _ = ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
          variation inputRow inputColumn •
            operator point (finiteMatrixUnit dimension inputRow inputColumn) := by
        apply Finset.sum_congr rfl
        intro inputRow _
        apply Finset.sum_congr rfl
        intro inputColumn _
        exact (operator point).map_smul _ _
  have hEntry := congrArg (fun matrix : MatrixN dimension =>
    matrix outputRow outputColumn) hExpansion
  simpa [finiteMatrixOperatorCoefficient_apply, Matrix.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using hEntry.symm

theorem smoothFiniteMatrixOperatorApply_value
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (variation : SmoothFiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension operator variation) point =
      operator point
        (smoothFiniteMatrixValue period hPeriod dimension variation point) := by
  ext outputRow outputColumn
  change (∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
      smoothScalarFieldMul period hPeriod
          (finiteMatrixOperatorCoefficient period hPeriod dimension operator
            outputRow outputColumn inputRow inputColumn)
          (variation inputRow inputColumn)) point = _
  simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
  exact finiteMatrixOperatorCoefficient_expansion
    period hPeriod dimension operator point
      (smoothFiniteMatrixValue period hPeriod dimension variation point)
      outputRow outputColumn

theorem smoothFiniteMatrixOperatorApply_comp
    (dimension : Nat)
    (first second : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hComp : ∀ point matrix, first point (second point matrix) = matrix)
    (variation : SmoothFiniteMatrix period hPeriod dimension) :
    smoothFiniteMatrixOperatorApply period hPeriod dimension first
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension second variation) = variation := by
  funext outputRow outputColumn
  apply SmoothQuotientField.ext
  intro point
  have hFirst := smoothFiniteMatrixOperatorApply_value
    period hPeriod dimension first
      (smoothFiniteMatrixOperatorApply
        period hPeriod dimension second variation) point
  rw [smoothFiniteMatrixOperatorApply_value
    period hPeriod dimension second variation point] at hFirst
  exact congrArg (fun matrix : MatrixN dimension =>
    matrix outputRow outputColumn) (hFirst.trans (hComp point _))

/-- Pointwise composition identities extend from the dense smooth core to
the full strong finite-matrix core. -/
theorem strongFiniteMatrixOperator_comp
    (dimension : Nat)
    (first second : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hComp : ∀ point matrix, first point (second point matrix) = matrix)
    (variation : StrongFiniteMatrix period hPeriod dimension) :
    strongFiniteMatrixOperator period hPeriod dimension first
        (strongFiniteMatrixOperator period hPeriod dimension second variation) =
      variation := by
  let firstStrong := strongFiniteMatrixOperator
    period hPeriod dimension first
  let secondStrong := strongFiniteMatrixOperator
    period hPeriod dimension second
  refine DenseRange.induction_on
    (smoothFiniteMatrixToStrong_denseRange period hPeriod dimension) variation
    (isClosed_eq (firstStrong.comp secondStrong).continuous
      (ContinuousLinearMap.id Real
        (StrongFiniteMatrix period hPeriod dimension)).continuous) ?_
  intro smooth
  change firstStrong (secondStrong
      (smoothFiniteMatrixToStrong period hPeriod dimension smooth)) =
    smoothFiniteMatrixToStrong period hPeriod dimension smooth
  rw [show secondStrong
      (smoothFiniteMatrixToStrong period hPeriod dimension smooth) =
      smoothFiniteMatrixToStrong period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension second smooth) from
    strongFiniteMatrixOperator_smooth
      period hPeriod dimension second smooth]
  rw [show firstStrong
      (smoothFiniteMatrixToStrong period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension second smooth)) =
      smoothFiniteMatrixToStrong period hPeriod dimension
        (smoothFiniteMatrixOperatorApply period hPeriod dimension first
          (smoothFiniteMatrixOperatorApply
            period hPeriod dimension second smooth)) from
    strongFiniteMatrixOperator_smooth period hPeriod dimension first _]
  rw [smoothFiniteMatrixOperatorApply_comp
    period hPeriod dimension first second hComp smooth]

theorem strongFiniteMatrixInverseOperator_left
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (variation : StrongFiniteMatrix period hPeriod dimension) :
    strongFiniteMatrixOperator period hPeriod dimension
        (pointwiseFiniteMatrixInverseField
          period hPeriod dimension operator hRegular)
        (strongFiniteMatrixOperator
          period hPeriod dimension operator variation) = variation := by
  exact strongFiniteMatrixOperator_comp period hPeriod dimension
    (pointwiseFiniteMatrixInverseField
      period hPeriod dimension operator hRegular) operator
    (pointwiseFiniteMatrixInverseField_left
      period hPeriod dimension operator hRegular) variation

theorem strongFiniteMatrixInverseOperator_right
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (variation : StrongFiniteMatrix period hPeriod dimension) :
    strongFiniteMatrixOperator period hPeriod dimension operator
        (strongFiniteMatrixOperator period hPeriod dimension
          (pointwiseFiniteMatrixInverseField
            period hPeriod dimension operator hRegular) variation) = variation := by
  exact strongFiniteMatrixOperator_comp period hPeriod dimension operator
    (pointwiseFiniteMatrixInverseField
      period hPeriod dimension operator hRegular)
    (pointwiseFiniteMatrixInverseField_right
      period hPeriod dimension operator hRegular) variation

/-- Bounded equivalence on the strong core induced by a smooth pointwise
bijective finite-matrix operator family. -/
def strongFiniteMatrixOperatorEquiv
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point)) :
    StrongFiniteMatrix period hPeriod dimension ≃L[Real]
      StrongFiniteMatrix period hPeriod dimension where
  toFun := strongFiniteMatrixOperator period hPeriod dimension operator
  invFun := strongFiniteMatrixOperator period hPeriod dimension
    (pointwiseFiniteMatrixInverseField
      period hPeriod dimension operator hRegular)
  left_inv := strongFiniteMatrixInverseOperator_left
    period hPeriod dimension operator hRegular
  right_inv := strongFiniteMatrixInverseOperator_right
    period hPeriod dimension operator hRegular
  map_add' first second := by simp
  map_smul' scalar variation := by simp
  continuous_toFun :=
    (strongFiniteMatrixOperator period hPeriod dimension operator).continuous
  continuous_invFun :=
    (strongFiniteMatrixOperator period hPeriod dimension
      (pointwiseFiniteMatrixInverseField
        period hPeriod dimension operator hRegular)).continuous

theorem strongFiniteMatrixOperatorEquiv_forward_eq
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point)) :
    (strongFiniteMatrixOperatorEquiv
        period hPeriod dimension operator hRegular :
      StrongFiniteMatrix period hPeriod dimension →L[Real]
        StrongFiniteMatrix period hPeriod dimension) =
      strongFiniteMatrixOperator period hPeriod dimension operator :=
  rfl

/-- Summary gate: smooth pointwise finite-dimensional invertibility lifts to
a bounded equivalence of the canonical strong matrix core. -/
theorem strong_finite_matrix_linear_equiv_lift_gate
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point)) :
    ∃ equivalence :
        StrongFiniteMatrix period hPeriod dimension ≃L[Real]
          StrongFiniteMatrix period hPeriod dimension,
      (equivalence : StrongFiniteMatrix period hPeriod dimension →L[Real]
        StrongFiniteMatrix period hPeriod dimension) =
        strongFiniteMatrixOperator period hPeriod dimension operator := by
  exact ⟨strongFiniteMatrixOperatorEquiv
    period hPeriod dimension operator hRegular, rfl⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D
end JanusFormal

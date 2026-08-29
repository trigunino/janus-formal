import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D

/-!
# Smooth finite-matrix operator families on the uniform C² core

The already established smooth coefficient expansion and pointwise inverse
field are lifted through the C² Banach algebra.  Pointwise finite-dimensional
bijectivity therefore yields a bounded linear equivalence of C² matrix
fields, with no extra analytic assumption.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixLinearEquivLift4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Manifold ContDiff
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

/-- A smooth operator coefficient lifted to the uniform C² core. -/
def finiteMatrixOperatorCoefficientC2
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (outputRow outputColumn inputRow inputColumn : Fin dimension) :
    C2Scalar period hPeriod :=
  smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (finiteMatrixOperatorCoefficient period hPeriod dimension operator
      outputRow outputColumn inputRow inputColumn)

def c2FiniteMatrixOperatorCoordinate
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (outputRow outputColumn : Fin dimension) :
    C2FiniteMatrix period hPeriod dimension →L[Real]
      C2Scalar period hPeriod :=
  ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (finiteMatrixOperatorCoefficientC2 period hPeriod dimension operator
        outputRow outputColumn inputRow inputColumn)).comp
      ((ContinuousLinearMap.proj inputColumn :
          (Fin dimension → C2Scalar period hPeriod) →L[Real]
            C2Scalar period hPeriod).comp
        (ContinuousLinearMap.proj inputRow :
          C2FiniteMatrix period hPeriod dimension →L[Real]
            (Fin dimension → C2Scalar period hPeriod)))

/-- Bounded C² lift of a smooth pointwise finite-matrix operator family. -/
def c2FiniteMatrixOperator
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension)) :
    C2FiniteMatrix period hPeriod dimension →L[Real]
      C2FiniteMatrix period hPeriod dimension :=
  ContinuousLinearMap.pi fun outputRow : Fin dimension =>
    ContinuousLinearMap.pi fun outputColumn : Fin dimension =>
      c2FiniteMatrixOperatorCoordinate
        period hPeriod dimension operator outputRow outputColumn

@[simp]
theorem c2FiniteMatrixOperator_apply
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (variation : C2FiniteMatrix period hPeriod dimension)
    (outputRow outputColumn : Fin dimension) :
    c2FiniteMatrixOperator period hPeriod dimension operator variation
        outputRow outputColumn =
      ∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (finiteMatrixOperatorCoefficientC2
            period hPeriod dimension operator
              outputRow outputColumn inputRow inputColumn)
          (variation inputRow inputColumn) := by
  simp [c2FiniteMatrixOperator, c2FiniteMatrixOperatorCoordinate]

theorem c2FiniteMatrixOperator_smooth
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (variation : SmoothFiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixOperator period hPeriod dimension operator
        (smoothFiniteMatrixToC2 period hPeriod dimension variation) =
      smoothFiniteMatrixToC2 period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension operator variation) := by
  funext outputRow outputColumn
  rw [c2FiniteMatrixOperator_apply]
  change (∑ inputRow : Fin dimension, ∑ inputColumn : Fin dimension,
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (finiteMatrixOperatorCoefficient period hPeriod dimension operator
            outputRow outputColumn inputRow inputColumn))
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (variation inputRow inputColumn))) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
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
  exact canonicalPhysicalScalarC2JetCoreProduct_smooth
    period hPeriod
      (finiteMatrixOperatorCoefficient period hPeriod dimension operator
        outputRow outputColumn inputRow inputColumn)
      (variation inputRow inputColumn)

/-- Two bounded C² matrix operators that agree on the smooth dense core agree
everywhere. -/
theorem c2FiniteMatrixOperator_eq_of_smooth
    (dimension : Nat)
    (field : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (target : C2FiniteMatrix period hPeriod dimension →L[Real]
      C2FiniteMatrix period hPeriod dimension)
    (hCore : ∀ smooth : SmoothFiniteMatrix period hPeriod dimension,
      target (smoothFiniteMatrixToC2 period hPeriod dimension smooth) =
        smoothFiniteMatrixToC2 period hPeriod dimension
          (smoothFiniteMatrixOperatorApply
            period hPeriod dimension field smooth)) :
    c2FiniteMatrixOperator period hPeriod dimension field = target := by
  let abstract := c2FiniteMatrixOperator period hPeriod dimension field
  apply ContinuousLinearMap.ext
  intro matrix
  change abstract matrix = target matrix
  refine DenseRange.induction_on
    (smoothFiniteMatrixToC2_denseRange period hPeriod dimension) matrix
    (isClosed_eq abstract.continuous target.continuous) ?_
  intro smooth
  rw [show abstract
      (smoothFiniteMatrixToC2 period hPeriod dimension smooth) =
      smoothFiniteMatrixToC2 period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension field smooth) from
    c2FiniteMatrixOperator_smooth
      period hPeriod dimension field smooth]
  exact (hCore smooth).symm

/-- Pointwise composition identities extend from smooth matrices to the full
C² matrix core by density. -/
theorem c2FiniteMatrixOperator_comp
    (dimension : Nat)
    (first second : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hComp : ∀ point matrix, first point (second point matrix) = matrix)
    (variation : C2FiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixOperator period hPeriod dimension first
        (c2FiniteMatrixOperator period hPeriod dimension second variation) =
      variation := by
  let firstC2 := c2FiniteMatrixOperator
    period hPeriod dimension first
  let secondC2 := c2FiniteMatrixOperator
    period hPeriod dimension second
  refine DenseRange.induction_on
    (smoothFiniteMatrixToC2_denseRange period hPeriod dimension) variation
    (isClosed_eq (firstC2.comp secondC2).continuous
      (ContinuousLinearMap.id Real
        (C2FiniteMatrix period hPeriod dimension)).continuous) ?_
  intro smooth
  change firstC2 (secondC2
      (smoothFiniteMatrixToC2 period hPeriod dimension smooth)) =
    smoothFiniteMatrixToC2 period hPeriod dimension smooth
  rw [show secondC2
      (smoothFiniteMatrixToC2 period hPeriod dimension smooth) =
      smoothFiniteMatrixToC2 period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension second smooth) from
    c2FiniteMatrixOperator_smooth
      period hPeriod dimension second smooth]
  rw [show firstC2
      (smoothFiniteMatrixToC2 period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension second smooth)) =
      smoothFiniteMatrixToC2 period hPeriod dimension
        (smoothFiniteMatrixOperatorApply period hPeriod dimension first
          (smoothFiniteMatrixOperatorApply
            period hPeriod dimension second smooth)) from
    c2FiniteMatrixOperator_smooth period hPeriod dimension first _]
  rw [smoothFiniteMatrixOperatorApply_comp
    period hPeriod dimension first second hComp smooth]

theorem c2FiniteMatrixInverseOperator_left
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (variation : C2FiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixOperator period hPeriod dimension
        (pointwiseFiniteMatrixInverseField
          period hPeriod dimension operator hRegular)
        (c2FiniteMatrixOperator
          period hPeriod dimension operator variation) = variation :=
  c2FiniteMatrixOperator_comp period hPeriod dimension
    (pointwiseFiniteMatrixInverseField
      period hPeriod dimension operator hRegular) operator
    (pointwiseFiniteMatrixInverseField_left
      period hPeriod dimension operator hRegular) variation

theorem c2FiniteMatrixInverseOperator_right
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point))
    (variation : C2FiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixOperator period hPeriod dimension operator
        (c2FiniteMatrixOperator period hPeriod dimension
          (pointwiseFiniteMatrixInverseField
            period hPeriod dimension operator hRegular) variation) = variation :=
  c2FiniteMatrixOperator_comp period hPeriod dimension operator
    (pointwiseFiniteMatrixInverseField
      period hPeriod dimension operator hRegular)
    (pointwiseFiniteMatrixInverseField_right
      period hPeriod dimension operator hRegular) variation

/-- Bounded equivalence on C² matrices induced by a pointwise bijective
smooth finite-dimensional operator family. -/
def c2FiniteMatrixOperatorEquiv
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point)) :
    C2FiniteMatrix period hPeriod dimension ≃L[Real]
      C2FiniteMatrix period hPeriod dimension where
  toFun := c2FiniteMatrixOperator period hPeriod dimension operator
  invFun := c2FiniteMatrixOperator period hPeriod dimension
    (pointwiseFiniteMatrixInverseField
      period hPeriod dimension operator hRegular)
  left_inv := c2FiniteMatrixInverseOperator_left
    period hPeriod dimension operator hRegular
  right_inv := c2FiniteMatrixInverseOperator_right
    period hPeriod dimension operator hRegular
  map_add' first second := by simp
  map_smul' scalar variation := by simp
  continuous_toFun :=
    (c2FiniteMatrixOperator period hPeriod dimension operator).continuous
  continuous_invFun :=
    (c2FiniteMatrixOperator period hPeriod dimension
      (pointwiseFiniteMatrixInverseField
        period hPeriod dimension operator hRegular)).continuous

theorem c2FiniteMatrixOperatorEquiv_forward_eq
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point)) :
    (c2FiniteMatrixOperatorEquiv
        period hPeriod dimension operator hRegular :
      C2FiniteMatrix period hPeriod dimension →L[Real]
        C2FiniteMatrix period hPeriod dimension) =
      c2FiniteMatrixOperator period hPeriod dimension operator :=
  rfl

/-- Summary gate: existing pointwise invertibility lifts faithfully to the
uniform C² matrix completion. -/
theorem canonical_physical_c2_finite_matrix_linear_equiv_lift_gate
    (dimension : Nat)
    (operator : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (hRegular : ∀ point, Function.Bijective (operator point)) :
    ∃ equivalence :
        C2FiniteMatrix period hPeriod dimension ≃L[Real]
          C2FiniteMatrix period hPeriod dimension,
      (equivalence : C2FiniteMatrix period hPeriod dimension →L[Real]
        C2FiniteMatrix period hPeriod dimension) =
        c2FiniteMatrixOperator period hPeriod dimension operator := by
  exact ⟨c2FiniteMatrixOperatorEquiv
    period hPeriod dimension operator hRegular, rfl⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixLinearEquivLift4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRootDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Jacobi derivative of the finite C² determinant at the identity -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix (dimension : Nat) :=
  C2FiniteMatrix period hPeriod dimension

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

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance c2ScalarCommRing : CommRing (C2Scalar period hPeriod) where
  toAddCommGroup := inferInstance
  mul := fun first second =>
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second
  mul_assoc := c2ScalarProduct_assoc period hPeriod
  one := c2ScalarOne period hPeriod
  one_mul := c2ScalarOne_mul period hPeriod
  mul_one := c2Scalar_mul_one period hPeriod
  mul_comm := c2ScalarProduct_comm period hPeriod
  left_distrib first second third :=
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first).map_add
      second third
  right_distrib first second third :=
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip third
      |>.map_add first second
  zero_mul field :=
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip field
      |>.map_zero
  mul_zero field :=
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod field).map_zero

/-- Continuous trace in the completed finite C² matrix algebra. -/
def c2FiniteMatrixTrace (dimension : Nat) :
    C2Matrix period hPeriod dimension →L[Real] C2Scalar period hPeriod :=
  ∑ index : Fin dimension,
    (ContinuousLinearMap.proj index :
      (Fin dimension → C2Scalar period hPeriod) →L[Real]
        C2Scalar period hPeriod).comp
      (ContinuousLinearMap.proj index :
        C2Matrix period hPeriod dimension →L[Real]
          (Fin dimension → C2Scalar period hPeriod))

@[simp]
theorem c2FiniteMatrixTrace_apply (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) :
    c2FiniteMatrixTrace period hPeriod dimension matrix =
      ∑ index : Fin dimension, matrix index index := by
  simp [c2FiniteMatrixTrace]

@[simp]
private theorem smoothFiniteMatrixToC2_apply (dimension : Nat)
    (matrix : SmoothFiniteMatrix period hPeriod dimension)
    (row column : Fin dimension) :
    smoothFiniteMatrixToC2 period hPeriod dimension matrix row column =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (matrix row column) :=
  rfl

private theorem c2FiniteMatrixIdentity_eq_diagonal (dimension : Nat) :
    c2FiniteMatrixIdentity period hPeriod dimension =
      Matrix.diagonal (fun _ : Fin dimension =>
        c2ScalarOne period hPeriod) := by
  funext row column
  unfold c2FiniteMatrixIdentity
  rw [smoothFiniteMatrixToC2_apply]
  rw [show smoothFiniteMatrixIdentity period hPeriod dimension row column =
      constantSmoothField period hPeriod Real
        (if row = column then 1 else 0) from rfl]
  by_cases h : row = column
  · subst column
    rw [Matrix.diagonal_apply_eq]
    rw [if_pos rfl]
    change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (constantSmoothField period hPeriod Real 1) =
      c2ScalarOne period hPeriod
    rfl
  · rw [Matrix.diagonal_apply_ne _ h]
    simp only [if_neg h]
    change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (constantSmoothField period hPeriod Real 0) = 0
    rw [show constantSmoothField period hPeriod Real 0 = 0 by
      apply SmoothQuotientField.ext period hPeriod Real
      intro point
      rfl]
    exact (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_zero

private theorem real_smul_one_mul (scalar : Real)
    (field : C2Scalar period hPeriod) :
    ((scalar • (1 : C2Scalar period hPeriod)) * field) = scalar • field := by
  change canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (scalar • c2ScalarOne period hPeriod) field = scalar • field
  calc
    _ = scalar • canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (c2ScalarOne period hPeriod) field :=
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip field
        |>.map_smul scalar (c2ScalarOne period hPeriod)
    _ = scalar • field := by rw [c2ScalarOne_mul]

private theorem c2Matrix_scalarUnit_smul (dimension : Nat) (scalar : Real)
    (matrix : C2Matrix period hPeriod dimension) :
    (scalar • (1 : C2Scalar period hPeriod)) • matrix = scalar • matrix := by
  funext row column
  change ((scalar • (1 : C2Scalar period hPeriod)) * matrix row column) =
    scalar • matrix row column
  exact real_smul_one_mul period hPeriod scalar (matrix row column)

private def c2FiniteMatrixRealLeibnizDeterminant (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) : C2Scalar period hPeriod :=
  ∑ permutation : Equiv.Perm (Fin dimension),
    (((Equiv.Perm.sign permutation : ℤ) : Real) •
      ∏ index : Fin dimension, matrix (permutation index) index)

private theorem c2FiniteMatrixDeterminant_eq_realLeibniz (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) :
    c2FiniteMatrixDeterminant period hPeriod dimension matrix =
      c2FiniteMatrixRealLeibnizDeterminant period hPeriod dimension matrix := by
  rfl

private theorem c2FiniteMatrixDeterminant_eq_det (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) :
    c2FiniteMatrixDeterminant period hPeriod dimension matrix =
      Matrix.det matrix := by
  rw [c2FiniteMatrixDeterminant_eq_realLeibniz, Matrix.det_apply']
  unfold c2FiniteMatrixRealLeibnizDeterminant
  apply Finset.sum_congr rfl
  intro permutation _
  rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with hSign | hSign
  · rw [hSign]
    simp
  · rw [hSign]
    norm_num

private theorem c2ScalarUnitPower_contDiff (power : Nat) :
    ContDiff Real ∞ (fun scalar : Real =>
      (scalar • (1 : C2Scalar period hPeriod)) ^ power) := by
  induction power with
  | zero =>
      simpa using (contDiff_const : ContDiff Real ∞
        (fun _ : Real => (1 : C2Scalar period hPeriod)))
  | succ power induction =>
      rw [show (fun scalar : Real =>
          (scalar • (1 : C2Scalar period hPeriod)) ^ (power + 1)) =
        fun scalar => canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          ((scalar • (1 : C2Scalar period hPeriod)) ^ power)
          (scalar • (1 : C2Scalar period hPeriod)) by
        funext scalar
        exact pow_succ _ _]
      exact ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod).contDiff
        |>.fun_comp induction).clm_apply
          (contDiff_id.smul_const (1 : C2Scalar period hPeriod))

private theorem c2PolynomialAlongUnit_contDiff
    (polynomial : Polynomial (C2Scalar period hPeriod)) :
    ContDiff Real ∞ (fun scalar : Real =>
      polynomial.eval (scalar • (1 : C2Scalar period hPeriod))) := by
  induction polynomial using Polynomial.induction_on' with
  | add first second hFirst hSecond =>
      simpa only [Polynomial.eval_add] using hFirst.add hSecond
  | monomial power coefficient =>
      rw [show (fun scalar : Real =>
          (Polynomial.monomial power coefficient).eval
            (scalar • (1 : C2Scalar period hPeriod))) =
        fun scalar => canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          coefficient ((scalar • (1 : C2Scalar period hPeriod)) ^ power) by
        funext scalar
        exact Polynomial.eval_monomial]
      exact (canonicalPhysicalScalarC2JetCoreProduct period hPeriod coefficient)
        |>.contDiff.comp (c2ScalarUnitPower_contDiff period hPeriod power)

private theorem c2FiniteMatrixDeterminant_line_taylor (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) (scalar : Real) :
    c2FiniteMatrixDeterminant period hPeriod dimension
        (c2FiniteMatrixIdentity period hPeriod dimension + scalar • matrix) =
      (1 : C2Scalar period hPeriod) +
        Matrix.trace matrix * (scalar • (1 : C2Scalar period hPeriod)) +
        (Matrix.det
            (1 + (Polynomial.X :
              Polynomial (C2Scalar period hPeriod)) •
                Matrix.map matrix Polynomial.C)).divX.divX.eval
              (scalar • (1 : C2Scalar period hPeriod)) *
          (scalar • (1 : C2Scalar period hPeriod)) ^ 2 := by
  rw [c2FiniteMatrixDeterminant_eq_det,
    c2FiniteMatrixIdentity_eq_diagonal]
  have hOne : Matrix.diagonal (fun _ : Fin dimension =>
      c2ScalarOne period hPeriod) =
      (1 : Matrix (Fin dimension) (Fin dimension)
        (C2Scalar period hPeriod)) := rfl
  rw [hOne]
  rw [← c2Matrix_scalarUnit_smul period hPeriod dimension scalar matrix]
  exact Matrix.det_one_add_smul
    (scalar • (1 : C2Scalar period hPeriod)) matrix

private theorem c2ScalarUnitLine_hasDerivAt :
    HasDerivAt (fun scalar : Real =>
      scalar • (1 : C2Scalar period hPeriod))
      (1 : C2Scalar period hPeriod) 0 := by
  simpa using (hasDerivAt_id (0 : Real)).smul_const
    (1 : C2Scalar period hPeriod)

private theorem c2ScalarUnitSquare_hasDerivAt_zero :
    HasDerivAt (fun scalar : Real =>
      (scalar • (1 : C2Scalar period hPeriod)) ^ 2)
      (0 : C2Scalar period hPeriod) 0 := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  have hUnit := c2ScalarUnitLine_hasDerivAt period hPeriod
  have hProduct :=
    ((product.hasFDerivAt.comp 0 hUnit.hasFDerivAt).clm_apply
      hUnit.hasFDerivAt).hasDerivAt
  simp only [pow_two]
  change HasDerivAt (fun scalar : Real =>
    product (scalar • (1 : C2Scalar period hPeriod))
      (scalar • (1 : C2Scalar period hPeriod))) 0 0
  apply hProduct.congr_deriv
  simp only [Function.comp_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one, zero_smul]
  rw [product.map_zero]
  simp only [zero_apply, zero_add]
  exact (product _).map_zero

private theorem c2DeterminantRemainder_hasDerivAt_zero (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) :
    HasDerivAt
      (fun scalar : Real =>
        (Matrix.det
            (1 + (Polynomial.X :
              Polynomial (C2Scalar period hPeriod)) •
                Matrix.map matrix Polynomial.C)).divX.divX.eval
              (scalar • (1 : C2Scalar period hPeriod)) *
          (scalar • (1 : C2Scalar period hPeriod)) ^ 2)
      (0 : C2Scalar period hPeriod) 0 := by
  let polynomial : Polynomial (C2Scalar period hPeriod) :=
    (Matrix.det
      (1 + (Polynomial.X : Polynomial (C2Scalar period hPeriod)) •
        Matrix.map matrix Polynomial.C)).divX.divX
  have hFirst :=
    (((c2PolynomialAlongUnit_contDiff period hPeriod polynomial).differentiable
      (by simp)) 0).hasFDerivAt
  have hSecond :=
    (c2ScalarUnitSquare_hasDerivAt_zero period hPeriod).hasFDerivAt
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  have hProduct :=
    ((product.hasFDerivAt.comp 0 hFirst).clm_apply hSecond).hasDerivAt
  change HasDerivAt (fun scalar : Real =>
    product (polynomial.eval (scalar • (1 : C2Scalar period hPeriod)))
      ((scalar • (1 : C2Scalar period hPeriod)) ^ 2)) 0 0
  apply hProduct.congr_deriv
  simp only [Function.comp_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul,
    map_zero, zero_add]
  rw [zero_pow (by norm_num : (2 : Nat) ≠ 0)]
  exact (product _).map_zero

private theorem c2DeterminantLinearTerm_hasDerivAt (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) :
    HasDerivAt
      (fun scalar : Real =>
        (1 : C2Scalar period hPeriod) +
          Matrix.trace matrix *
            (scalar • (1 : C2Scalar period hPeriod)))
      (Matrix.trace matrix) 0 := by
  have hStandard :=
    (hasDerivAt_const (0 : Real)
        (1 : C2Scalar period hPeriod)).add
      ((hasDerivAt_id (0 : Real)).smul_const (Matrix.trace matrix))
  refine (hStandard.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [zero_add, one_smul]
  · apply Filter.Eventually.of_forall
    intro scalar
    simp only [Pi.add_apply, id_eq]
    rw [mul_comm, real_smul_one_mul]

/-- Exact Jacobi derivative on every affine line through the C² identity. -/
theorem c2FiniteMatrixDeterminant_line_hasDerivAt (dimension : Nat)
    (matrix : C2Matrix period hPeriod dimension) :
    HasDerivAt
      (fun scalar : Real =>
        c2FiniteMatrixDeterminant period hPeriod dimension
          (c2FiniteMatrixIdentity period hPeriod dimension + scalar • matrix))
      (c2FiniteMatrixTrace period hPeriod dimension matrix) 0 := by
  have hTrace :
      c2FiniteMatrixTrace period hPeriod dimension matrix =
        Matrix.trace matrix := by
    rw [c2FiniteMatrixTrace_apply]
    rfl
  have hExpansion :=
    (c2DeterminantLinearTerm_hasDerivAt
      period hPeriod dimension matrix).add
        (c2DeterminantRemainder_hasDerivAt_zero
          period hPeriod dimension matrix)
  have hDeterminant :
      HasDerivAt
        (fun scalar : Real =>
          c2FiniteMatrixDeterminant period hPeriod dimension
            (c2FiniteMatrixIdentity period hPeriod dimension +
              scalar • matrix))
        (Matrix.trace matrix) 0 :=
    (hExpansion.congr_deriv (add_zero _)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun scalar =>
        c2FiniteMatrixDeterminant_line_taylor
          period hPeriod dimension matrix scalar)
  exact hDeterminant.congr_deriv hTrace.symm

private theorem c2MatrixAffineLine_hasDerivAt (dimension : Nat)
    (base direction : C2Matrix period hPeriod dimension) :
    HasDerivAt (fun scalar : Real => base + scalar • direction)
      direction 0 := by
  have hAffine :=
    (hasDerivAt_const (0 : Real) base).add
      ((hasDerivAt_id (0 : Real)).smul_const direction)
  refine (hAffine.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [zero_add, one_smul]
  · apply Filter.Eventually.of_forall
    intro scalar
    simp only [Pi.add_apply, id_eq]

/-- The Fréchet derivative of the finite C² determinant at the identity is trace. -/
theorem c2FiniteMatrixDeterminant_hasFDerivAt_identity (dimension : Nat) :
    HasFDerivAt
      (c2FiniteMatrixDeterminant period hPeriod dimension)
      (c2FiniteMatrixTrace period hPeriod dimension)
      (c2FiniteMatrixIdentity period hPeriod dimension) := by
  let determinant := c2FiniteMatrixDeterminant period hPeriod dimension
  let identity := c2FiniteMatrixIdentity period hPeriod dimension
  have hDifferentiable : DifferentiableAt Real determinant identity :=
    ((c2FiniteMatrixDeterminant_contDiff period hPeriod dimension).differentiable
      (by simp)) identity
  have hCanonical := hDifferentiable.hasFDerivAt
  apply hCanonical.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  have hAffine := c2MatrixAffineLine_hasDerivAt
    period hPeriod dimension identity direction
  have hAtLineZero :
      HasFDerivAt determinant (fderiv Real determinant identity)
        ((fun scalar : Real => identity + scalar • direction) 0) := by
    simpa using hCanonical
  have hComposed :=
    (hAtLineZero.comp 0 hAffine.hasFDerivAt).hasDerivAt
  have hLine := c2FiniteMatrixDeterminant_line_hasDerivAt
    period hPeriod dimension direction
  have hUnique := hComposed.unique hLine
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one] using hUnique

/-- Gate marker for the exact Jacobi derivative in the completed C² algebra. -/
theorem canonical_physical_c2_finite_matrix_determinant_derivative_gate
    (dimension : Nat) :
    HasFDerivAt
      (c2FiniteMatrixDeterminant period hPeriod dimension)
      (c2FiniteMatrixTrace period hPeriod dimension)
      (c2FiniteMatrixIdentity period hPeriod dimension) :=
  c2FiniteMatrixDeterminant_hasFDerivAt_identity
    period hPeriod dimension

end
end P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
end JanusFormal

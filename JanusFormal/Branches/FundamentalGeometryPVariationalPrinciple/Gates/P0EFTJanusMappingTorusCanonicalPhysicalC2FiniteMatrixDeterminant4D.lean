import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant on finite matrices over the canonical C² core

The exact commutative scalar Leibniz product defines the finite Leibniz
determinant directly.  It is a smooth polynomial, agrees with the ordinary
pointwise determinant on every genuine smooth matrix, and sends the completed
identity matrix to the scalar unit.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

local instance smoothScalarCommMonoid :
    CommMonoid (SmoothQuotientField period hPeriod Real) where
  mul := fun first second => smoothScalarFieldMul period hPeriod first second
  one := smoothScalarOne period hPeriod
  mul_assoc :=
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldMul_assoc
      period hPeriod
  one_mul := smoothScalarOne_mul period hPeriod
  mul_one := smoothScalar_mul_one period hPeriod
  mul_comm first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    exact mul_comm _ _

local instance c2ScalarCommMonoid : CommMonoid (C2Scalar period hPeriod) where
  mul := fun first second =>
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second
  one := c2ScalarOne period hPeriod
  mul_assoc := c2ScalarProduct_assoc period hPeriod
  one_mul := c2ScalarOne_mul period hPeriod
  mul_one := c2Scalar_mul_one period hPeriod
  mul_comm := c2ScalarProduct_comm period hPeriod

private def permutationSignReal {dimension : Nat}
    (permutation : Equiv.Perm (Fin dimension)) : Real :=
  ((Equiv.Perm.sign permutation : ℤ) : Real)

/-- Smooth Leibniz determinant of a finite smooth scalar matrix. -/
def smoothFiniteMatrixDeterminant (dimension : Nat)
    (matrix : SmoothFiniteMatrix period hPeriod dimension) :
    SmoothQuotientField period hPeriod Real :=
  ∑ permutation : Equiv.Perm (Fin dimension),
    permutationSignReal permutation •
      ∏ index : Fin dimension, matrix (permutation index) index

/-- Leibniz determinant in the completed scalar C² algebra. -/
def c2FiniteMatrixDeterminant (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension) :
    C2Scalar period hPeriod :=
  ∑ permutation : Equiv.Perm (Fin dimension),
    permutationSignReal permutation •
      ∏ index : Fin dimension, matrix (permutation index) index

private theorem smoothScalarFinsetProduct_apply
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index)
    (fields : Index → SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    (∏ index ∈ indices, fields index) point =
      ∏ index ∈ indices, fields index point := by
  induction indices using Finset.induction_on with
  | empty =>
      change smoothScalarOne period hPeriod point = 1
      rfl
  | @insert index indices hIndex hInduction =>
      rw [Finset.prod_insert hIndex]
      change smoothScalarFieldMul period hPeriod
          (fields index) (∏ current ∈ indices, fields current) point = _
      rw [smoothScalarFieldMul_apply, hInduction]
      rw [Finset.prod_insert hIndex]

theorem smoothFiniteMatrixDeterminant_apply
    (dimension : Nat)
    (matrix : SmoothFiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixDeterminant
        period hPeriod dimension matrix point =
      Matrix.det (fun row column => matrix row column point) := by
  rw [Matrix.det_apply']
  simp only [smoothFiniteMatrixDeterminant,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldSmul_toFun, smoothScalarFinsetProduct_apply]
  apply Finset.sum_congr rfl
  intro permutation _
  rfl

/-- The exact smooth lift is a multiplicative map for the local scalar
commutative monoids. -/
def smoothScalarToC2MonoidHom :
    SmoothQuotientField period hPeriod Real →*
      C2Scalar period hPeriod where
  toFun := smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
  map_one' := rfl
  map_mul' first second := by
    change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothScalarFieldMul period hPeriod first second) =
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod first)
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod second)
    exact (canonicalPhysicalScalarC2JetCoreProduct_smooth
      period hPeriod first second).symm

theorem c2FiniteMatrixDeterminant_smooth
    (dimension : Nat)
    (matrix : SmoothFiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixDeterminant period hPeriod dimension
        (smoothFiniteMatrixToC2 period hPeriod dimension matrix) =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothFiniteMatrixDeterminant
          period hPeriod dimension matrix) := by
  unfold c2FiniteMatrixDeterminant smoothFiniteMatrixDeterminant
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro permutation _
  rw [map_smul]
  apply congrArg (permutationSignReal permutation • ·)
  exact (map_prod
    (smoothScalarToC2MonoidHom period hPeriod)
    (fun index : Fin dimension => matrix (permutation index) index)
    Finset.univ).symm

private theorem c2MatrixPermutationProduct_contDiff
    (dimension : Nat)
    (permutation : Equiv.Perm (Fin dimension)) :
    ContDiff Real ∞
      (fun matrix : C2FiniteMatrix period hPeriod dimension =>
        ∏ index : Fin dimension, matrix (permutation index) index) := by
  classical
  let indices : Finset (Fin dimension) := Finset.univ
  change ContDiff Real ∞
    (fun matrix : C2FiniteMatrix period hPeriod dimension =>
      ∏ index ∈ indices, matrix (permutation index) index)
  induction indices using Finset.induction_on with
  | empty =>
      change ContDiff Real ∞
        (fun _ : C2FiniteMatrix period hPeriod dimension =>
          c2ScalarOne period hPeriod)
      exact contDiff_const
  | @insert index indices hIndex hInduction =>
      rw [show (fun matrix : C2FiniteMatrix period hPeriod dimension =>
          ∏ current ∈ insert index indices,
            matrix (permutation current) current) =
        fun matrix => matrix (permutation index) index *
          ∏ current ∈ indices,
            matrix (permutation current) current by
        funext matrix
        rw [Finset.prod_insert hIndex]]
      have hEntry : ContDiff Real ∞
          (fun matrix : C2FiniteMatrix period hPeriod dimension =>
            matrix (permutation index) index) :=
        contDiff_apply_apply Real (C2Scalar period hPeriod)
          (permutation index) index
      exact ((canonicalPhysicalScalarC2JetCoreProduct
        period hPeriod).contDiff.fun_comp hEntry).clm_apply hInduction

theorem c2FiniteMatrixDeterminant_contDiff (dimension : Nat) :
    ContDiff Real ∞
      (c2FiniteMatrixDeterminant period hPeriod dimension) := by
  unfold c2FiniteMatrixDeterminant
  apply ContDiff.sum
  intro permutation _
  exact (contDiff_const : ContDiff Real ∞
      (fun _ : C2FiniteMatrix period hPeriod dimension =>
        permutationSignReal permutation)).smul
    (c2MatrixPermutationProduct_contDiff period hPeriod dimension permutation)

theorem smoothFiniteMatrixDeterminant_identity (dimension : Nat) :
    smoothFiniteMatrixDeterminant period hPeriod dimension
        (smoothFiniteMatrixIdentity period hPeriod dimension) =
      smoothScalarOne period hPeriod := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [smoothFiniteMatrixDeterminant_apply]
  have hIdentity :
      (fun row column =>
        smoothFiniteMatrixIdentity period hPeriod dimension row column point) =
        (1 : Matrix (Fin dimension) (Fin dimension) Real) := by
    funext row column
    simp [smoothFiniteMatrixIdentity, constantSmoothField,
      Matrix.one_apply]
  rw [hIdentity, Matrix.det_one]
  rfl

theorem c2FiniteMatrixDeterminant_identity (dimension : Nat) :
    c2FiniteMatrixDeterminant period hPeriod dimension
        (c2FiniteMatrixIdentity period hPeriod dimension) =
      c2ScalarOne period hPeriod := by
  rw [c2FiniteMatrixIdentity,
    c2FiniteMatrixDeterminant_smooth,
    smoothFiniteMatrixDeterminant_identity]
  rfl

/-- Summary gate for the finite C² determinant polynomial. -/
theorem canonical_physical_c2_finite_matrix_determinant_gate
    (dimension : Nat) :
    ContDiff Real ∞
        (c2FiniteMatrixDeterminant period hPeriod dimension) ∧
      c2FiniteMatrixDeterminant period hPeriod dimension
          (c2FiniteMatrixIdentity period hPeriod dimension) =
        c2ScalarOne period hPeriod ∧
      (∀ matrix : SmoothFiniteMatrix period hPeriod dimension,
        c2FiniteMatrixDeterminant period hPeriod dimension
            (smoothFiniteMatrixToC2 period hPeriod dimension matrix) =
          smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
            (smoothFiniteMatrixDeterminant
              period hPeriod dimension matrix)) := by
  exact ⟨c2FiniteMatrixDeterminant_contDiff
      period hPeriod dimension,
    c2FiniteMatrixDeterminant_identity period hPeriod dimension,
    c2FiniteMatrixDeterminant_smooth period hPeriod dimension⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
end JanusFormal

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurBlockElimination4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurNondegenerate4D

/-!
# Determinant criterion for finite Schur nondegeneracy

The finite Schur operator acts on `Mode → ℝ`.  Its standard-basis matrix has a
nonzero determinant exactly on the zero-mode-free stratum.  A nonzero
determinant gives the nonsingular matrix inverse, hence bijectivity of the Schur
operator and then bijectivity of the complete operator through the Schur
factorization.

Thus the infinite-dimensional nondegeneracy question is reduced to one finite
determinant calculation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurDeterminant4D

set_option autoImplicit false
noncomputable section

open Matrix
open P0EFTJanusProgramPFiniteModeSchurKernel4D
open P0EFTJanusProgramPFiniteModeSchurBlockElimination4D
open P0EFTJanusProgramPFiniteModeSchurNondegenerate4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Standard-basis matrix of the finite Schur operator. -/
def finiteModeSchurMatrix
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurBlockData operator Mode Complement) :
    Matrix Mode Mode Real :=
  LinearMap.toMatrix' (finiteModeSchurBlockOperator data)

@[simp]
theorem finiteModeSchurMatrix_mulVec
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurBlockData operator Mode Complement)
    (vector : Mode → Real) :
    finiteModeSchurMatrix data *ᵥ vector =
      finiteModeSchurBlockOperator data vector := by
  unfold finiteModeSchurMatrix
  exact LinearMap.toMatrix'_mulVec _ _

/-- Four-block Schur data together with the finite determinant test. -/
structure FiniteModeSchurDeterminantData
    (operator : E →L[Real] E)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement] where
  blockData : FiniteModeSchurBlockData operator Mode Complement
  determinant_ne_zero : (finiteModeSchurMatrix blockData).det ≠ 0

/-- Nonzero determinant makes the finite Schur operator injective. -/
theorem finiteModeSchurBlockOperator_injective_of_det_ne_zero
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurDeterminantData operator Mode Complement) :
    Function.Injective (finiteModeSchurBlockOperator data.blockData) := by
  intro first second hEqual
  let matrix := finiteModeSchurMatrix data.blockData
  have hUnitDet : IsUnit matrix.det :=
    isUnit_iff_ne_zero.mpr data.determinant_ne_zero
  have hMatrix : matrix *ᵥ first = matrix *ᵥ second := by
    simpa [matrix] using hEqual
  have hInverse := congrArg (fun vector => matrix⁻¹ *ᵥ vector) hMatrix
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul matrix hUnitDet] using
    hInverse

/-- Nonzero determinant makes the finite Schur operator surjective. -/
theorem finiteModeSchurBlockOperator_surjective_of_det_ne_zero
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurDeterminantData operator Mode Complement) :
    Function.Surjective (finiteModeSchurBlockOperator data.blockData) := by
  intro target
  let matrix := finiteModeSchurMatrix data.blockData
  have hUnitDet : IsUnit matrix.det :=
    isUnit_iff_ne_zero.mpr data.determinant_ne_zero
  refine ⟨matrix⁻¹ *ᵥ target, ?_⟩
  rw [← finiteModeSchurMatrix_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv matrix hUnitDet,
    Matrix.one_mulVec]

/-- Determinant criterion for finite Schur bijectivity. -/
theorem finiteModeSchurBlockOperator_bijective_of_det_ne_zero
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurDeterminantData operator Mode Complement) :
    Function.Bijective (finiteModeSchurBlockOperator data.blockData) :=
  ⟨finiteModeSchurBlockOperator_injective_of_det_ne_zero data,
    finiteModeSchurBlockOperator_surjective_of_det_ne_zero data⟩

/-- Convert the determinant test to the generic nondegenerate Schur packet. -/
def FiniteModeSchurDeterminantData.toNondegenerateData
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurDeterminantData operator Mode Complement) :
    FiniteModeSchurNondegenerateData operator Mode Complement where
  schurData := data.blockData.toKernelData
  schur_bijective :=
    finiteModeSchurBlockOperator_bijective_of_det_ne_zero data

section Complete

variable [CompleteSpace E]

/-- The full operator is invertible whenever the finite Schur determinant is
nonzero. -/
theorem finite_mode_schur_determinant_gate
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurDeterminantData operator Mode Complement) :
    Function.Bijective operator ∧
      operator.ker = ⊥ ∧
      Module.finrank Real operator.ker = 0 :=
  ⟨finiteModeSchur_operator_bijective data.toNondegenerateData,
    finiteModeSchur_operator_ker_eq_bot data.toNondegenerateData,
    finiteModeSchur_operator_kernel_finrank_zero data.toNondegenerateData⟩

end Complete

end
end P0EFTJanusProgramPFiniteModeSchurDeterminant4D
end JanusFormal

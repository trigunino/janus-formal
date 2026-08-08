import Mathlib.Analysis.Normed.Operator.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurDeterminant4D

/-!
# Explicit Green operator from the finite Schur formula

For a bounded four-block decomposition with nonzero finite Schur determinant,
the full inverse is not merely supplied by the bounded inverse theorem.  It is
the block Gaussian-elimination formula

`T⁻¹ R diag(S⁻¹, D⁻¹) L T`.

This file constructs that bounded operator and proves both inverse identities.
It therefore exposes the actual propagator in terms of the finite Schur inverse
and the inverse elliptic complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurExplicitGreen4D

set_option autoImplicit false
noncomputable section

open Matrix
open P0EFTJanusProgramPFiniteModeSchurBlockElimination4D
open P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
open P0EFTJanusProgramPFiniteModeSchurDeterminant4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Bounded four-block data on the nondegenerate Schur stratum. -/
structure FiniteModeSchurExplicitGreenData
    (operator : E →L[Real] E)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement] : Prop where
  blocks : FiniteModeContinuousSchurBlockData operator Mode Complement
  determinant_ne_zero :
    (finiteModeSchurMatrix blocks.toLinearBlockData).det ≠ 0

/-- Bounded inverse of the finite Schur block, written using the nonsingular
matrix inverse. -/
def finiteModeSchurFiniteInverse
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    (Mode → Real) →L[Real] (Mode → Real) :=
  (Matrix.toLin'
    (finiteModeSchurMatrix data.blocks.toLinearBlockData)⁻¹).toContinuousLinearMap

@[simp]
theorem finiteModeSchurFiniteInverse_apply
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (vector : Mode → Real) :
    finiteModeSchurFiniteInverse data vector =
      (finiteModeSchurMatrix data.blocks.toLinearBlockData)⁻¹ *ᵥ vector :=
  rfl

@[simp]
theorem finiteModeSchurFiniteInverse_schur
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (vector : Mode → Real) :
    finiteModeSchurFiniteInverse data
        (finiteModeSchurBlockOperator data.blocks.toLinearBlockData vector) =
      vector := by
  let matrix := finiteModeSchurMatrix data.blocks.toLinearBlockData
  have hUnit : IsUnit matrix.det :=
    isUnit_iff_ne_zero.mpr data.determinant_ne_zero
  change matrix⁻¹ *ᵥ (matrix *ᵥ vector) = vector
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul matrix hUnit,
    Matrix.one_mulVec]

@[simp]
theorem finiteModeSchur_schurFiniteInverse
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (vector : Mode → Real) :
    finiteModeSchurBlockOperator data.blocks.toLinearBlockData
        (finiteModeSchurFiniteInverse data vector) = vector := by
  let matrix := finiteModeSchurMatrix data.blocks.toLinearBlockData
  have hUnit : IsUnit matrix.det :=
    isUnit_iff_ne_zero.mpr data.determinant_ne_zero
  change matrix *ᵥ (matrix⁻¹ *ᵥ vector) = vector
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv matrix hUnit,
    Matrix.one_mulVec]

/-- Bounded right triangular reduction. -/
def finiteModeContinuousSchurRightReduction
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    ((Mode → Real) × Complement) →L[Real]
      ((Mode → Real) × Complement) :=
  let first := ContinuousLinearMap.fst Real (Mode → Real) Complement
  let second := ContinuousLinearMap.snd Real (Mode → Real) Complement
  let correction := data.blocks.complementEquiv.symm.toContinuousLinearMap.comp
    (data.blocks.lowerLeft.comp first)
  first.prod (second - correction)

@[simp]
theorem finiteModeContinuousSchurRightReduction_apply
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (state : (Mode → Real) × Complement) :
    finiteModeContinuousSchurRightReduction data state =
      finiteModeSchurRightReduction data.blocks.toLinearBlockData state :=
  rfl

/-- Inverse of the reduced diagonal block. -/
def finiteModeSchurDiagonalInverse
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    ((Mode → Real) × Complement) →L[Real]
      ((Mode → Real) × Complement) :=
  (finiteModeSchurFiniteInverse data).prodMap
    data.blocks.complementEquiv.symm.toContinuousLinearMap

@[simp]
theorem finiteModeSchurDiagonalInverse_diagonal
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (state : (Mode → Real) × Complement) :
    finiteModeSchurDiagonalInverse data
        (finiteModeSchurBlockOperator data.blocks.toLinearBlockData state.1,
          data.blocks.complementEquiv state.2) = state := by
  apply Prod.ext
  · exact finiteModeSchurFiniteInverse_schur data state.1
  · exact data.blocks.complementEquiv.symm_apply_apply state.2

@[simp]
theorem finiteModeSchur_diagonalDiagonalInverse
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (state : (Mode → Real) × Complement) :
    (finiteModeSchurBlockOperator data.blocks.toLinearBlockData
        (finiteModeSchurDiagonalInverse data state).1,
      data.blocks.complementEquiv
        (finiteModeSchurDiagonalInverse data state).2) = state := by
  apply Prod.ext
  · exact finiteModeSchur_schurFiniteInverse data state.1
  · exact data.blocks.complementEquiv.apply_symm_apply state.2

/-- Explicit bounded Green formula
`T⁻¹ R diag(S⁻¹,D⁻¹) L T`. -/
def finiteModeSchurExplicitGreen
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    E →L[Real] E :=
  data.blocks.decomposition.symm.toContinuousLinearMap.comp
    ((finiteModeContinuousSchurRightReduction data).comp
      ((finiteModeSchurDiagonalInverse data).comp
        ((finiteModeContinuousSchurLeftReduction data.blocks).comp
          data.blocks.decomposition.toContinuousLinearMap)))

/-- Explicit Green is a left inverse of the full operator. -/
theorem finiteModeSchurExplicitGreen_operator
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (state : E) :
    finiteModeSchurExplicitGreen data (operator state) = state := by
  let reduced := data.blocks.toLinearBlockData.rightReduction.symm
    (data.blocks.toLinearBlockData.decomposition state)
  have hFactor := data.blocks.toLinearBlockData.factorization reduced
  change data.blocks.decomposition.symm
      (finiteModeContinuousSchurRightReduction data
        (finiteModeSchurDiagonalInverse data
          (finiteModeContinuousSchurLeftReduction data.blocks
            (data.blocks.decomposition (operator state))))) = state
  have hSource :
      data.blocks.decomposition.symm
        (data.blocks.toLinearBlockData.rightReduction reduced) = state := by
    simp [reduced]
  rw [← hSource]
  apply data.blocks.decomposition.symm.injective
  change finiteModeContinuousSchurRightReduction data
      (finiteModeSchurDiagonalInverse data
        (finiteModeContinuousSchurLeftReduction data.blocks
          (data.blocks.decomposition
            (operator
              (data.blocks.decomposition.symm
                (data.blocks.toLinearBlockData.rightReduction reduced)))))) =
    data.blocks.toLinearBlockData.rightReduction reduced
  rw [hFactor]
  rw [finiteModeSchurDiagonalInverse_diagonal]
  rfl

/-- Explicit Green is a right inverse of the full operator. -/
theorem finiteModeSchur_operator_explicitGreen
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement)
    (state : E) :
    operator (finiteModeSchurExplicitGreen data state) = state := by
  let reducedTarget := finiteModeContinuousSchurLeftReduction data.blocks
    (data.blocks.decomposition state)
  let reducedSource := finiteModeSchurDiagonalInverse data reducedTarget
  have hFactor := data.blocks.toLinearBlockData.factorization reducedSource
  apply data.blocks.decomposition.injective
  apply data.blocks.toLinearBlockData.leftReduction.injective
  change data.blocks.toLinearBlockData.leftReduction
      (data.blocks.decomposition
        (operator
          (data.blocks.decomposition.symm
            (data.blocks.toLinearBlockData.rightReduction reducedSource)))) =
    data.blocks.toLinearBlockData.leftReduction
      (data.blocks.decomposition state)
  rw [hFactor]
  change
    (finiteModeSchurBlockOperator data.blocks.toLinearBlockData reducedSource.1,
      data.blocks.complementEquiv reducedSource.2) = reducedTarget
  exact finiteModeSchur_diagonalDiagonalInverse data reducedTarget

/-- Public explicit propagator checkpoint. -/
theorem finite_mode_schur_explicit_green_gate
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    (∀ state, finiteModeSchurExplicitGreen data (operator state) = state) ∧
      (∀ state, operator (finiteModeSchurExplicitGreen data state) = state) :=
  ⟨finiteModeSchurExplicitGreen_operator data,
    finiteModeSchur_operator_explicitGreen data⟩

end
end P0EFTJanusProgramPFiniteModeSchurExplicitGreen4D
end JanusFormal

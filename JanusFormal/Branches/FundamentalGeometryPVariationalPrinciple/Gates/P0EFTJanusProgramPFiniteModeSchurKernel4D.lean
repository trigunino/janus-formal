import Mathlib.LinearAlgebra.Dimension.Finite
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelModel4D

/-!
# Finite-mode Schur reduction of an operator kernel

A direct classification of the kernel of an infinite-dimensional Hessian is
usually not the natural first analytic step.  One first splits off a finite
space of reference modes, eliminates an invertible infinite-dimensional
complement and obtains a finite Schur operator.

This file isolates the exact linear algebra of that reduction.  A pair of
triangular changes of coordinates identifies an operator with

`diag(S, D)`

where `S` acts on a finite coordinate space and `D` is bijective on the
complement.  The actual operator kernel is then linearly equivalent to
`ker S`.  In particular the actual kernel is finite-dimensional and its
dimension is bounded by the number of reference modes.

No spectral theorem, projective zero-mode ansatz or second completion is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurKernel4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteKernelModel4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Exact finite-mode block diagonalization.  The `leftReduction` and
`rightReduction` fields are the two triangular Gaussian-elimination changes of
coordinates; `factorization` states that they reduce the full operator to the
finite Schur block and a bijective complement block. -/
structure FiniteModeSchurKernelData
    (operator : E →L[Real] E)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement] where
  decomposition : E ≃ₗ[Real] ((Mode → Real) × Complement)
  leftReduction : ((Mode → Real) × Complement) ≃ₗ[Real]
    ((Mode → Real) × Complement)
  rightReduction : ((Mode → Real) × Complement) ≃ₗ[Real]
    ((Mode → Real) × Complement)
  schur : (Mode → Real) →ₗ[Real] (Mode → Real)
  complementOperator : Complement →ₗ[Real] Complement
  complement_bijective : Function.Bijective complementOperator
  factorization : ∀ state : (Mode → Real) × Complement,
    leftReduction
        (decomposition
          (operator (decomposition.symm (rightReduction state)))) =
      (schur state.1, complementOperator state.2)

/-- Coordinates after undoing the right triangular reduction. -/
def finiteModeSchurCoordinates
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    E ≃ₗ[Real] ((Mode → Real) × Complement) :=
  data.decomposition.trans data.rightReduction.symm

private theorem finiteModeSchur_diagonal_of_kernel
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement)
    (state : operator.ker) :
    let coordinate := finiteModeSchurCoordinates data state.1
    (data.schur coordinate.1,
      data.complementOperator coordinate.2) = 0 := by
  let coordinate := finiteModeSchurCoordinates data state.1
  have hOperator : operator state.1 = 0 :=
    LinearMap.mem_ker.mp state.2
  rw [← data.factorization coordinate]
  simp [coordinate, finiteModeSchurCoordinates, hOperator]

/-- Project an actual zero mode to its finite Schur coordinate. -/
def operatorKernelToSchurKernel
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement)
    (state : operator.ker) : data.schur.ker := by
  let coordinate := finiteModeSchurCoordinates data state.1
  have hDiagonal := finiteModeSchur_diagonal_of_kernel data state
  refine ⟨coordinate.1, ?_⟩
  apply LinearMap.mem_ker.mpr
  simpa [coordinate] using congrArg Prod.fst hDiagonal

/-- Reconstruct an actual zero mode from one Schur zero mode.  The complement
coordinate is forced to be `-D⁻¹ Cx` by the right triangular reduction already
stored in the factorization. -/
def schurKernelToOperatorKernel
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement)
    (state : data.schur.ker) : operator.ker := by
  let reduced : (Mode → Real) × Complement := (state.1, 0)
  let original : E := data.decomposition.symm (data.rightReduction reduced)
  refine ⟨original, ?_⟩
  apply LinearMap.mem_ker.mpr
  have hDiagonal :
      (data.schur reduced.1,
        data.complementOperator reduced.2) = 0 := by
    apply Prod.ext
    · simpa [reduced] using LinearMap.mem_ker.mp state.2
    · simp [reduced]
  have hLeft :
      data.leftReduction (data.decomposition (operator original)) = 0 := by
    exact (data.factorization reduced).trans hDiagonal
  have hDecomposition : data.decomposition (operator original) = 0 := by
    apply data.leftReduction.injective
    simpa using hLeft
  apply data.decomposition.injective
  simpa using hDecomposition

/-- The full operator kernel is exactly the finite Schur kernel. -/
noncomputable def finiteModeSchurKernelEquiv
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    operator.ker ≃ₗ[Real] data.schur.ker where
  toFun := operatorKernelToSchurKernel data
  invFun := schurKernelToOperatorKernel data
  map_add' := by
    intro first second
    apply Subtype.ext
    simp [operatorKernelToSchurKernel, finiteModeSchurCoordinates]
  map_smul' := by
    intro scalar state
    apply Subtype.ext
    simp [operatorKernelToSchurKernel, finiteModeSchurCoordinates]
  left_inv := by
    intro state
    apply Subtype.ext
    let coordinate := finiteModeSchurCoordinates data state.1
    have hDiagonal := finiteModeSchur_diagonal_of_kernel data state
    have hComplementImage : data.complementOperator coordinate.2 = 0 := by
      simpa [coordinate] using congrArg Prod.snd hDiagonal
    have hComplement : coordinate.2 = 0 := by
      apply data.complement_bijective.1
      simpa using hComplementImage
    change data.decomposition.symm
        (data.rightReduction
          ((finiteModeSchurCoordinates data state.1).1, 0)) = state.1
    have hCoordinate :
        ((finiteModeSchurCoordinates data state.1).1, 0) =
          finiteModeSchurCoordinates data state.1 := by
      apply Prod.ext
      · rfl
      · simpa [coordinate] using hComplement.symm
    rw [hCoordinate]
    simp [finiteModeSchurCoordinates]
  right_inv := by
    intro state
    apply Subtype.ext
    simp [operatorKernelToSchurKernel, schurKernelToOperatorKernel,
      finiteModeSchurCoordinates]

/-- Finite-dimensionality of the Schur kernel. -/
noncomputable def finiteModeSchurKernelFiniteDimensional
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    FiniteDimensional Real data.schur.ker := by
  infer_instance

/-- Finite-dimensionality of the actual operator kernel, derived rather than
supplied. -/
noncomputable def finiteModeSchurOperatorKernelFiniteDimensional
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    FiniteDimensional Real operator.ker := by
  letI : FiniteDimensional Real data.schur.ker :=
    finiteModeSchurKernelFiniteDimensional data
  exact (finiteModeSchurKernelEquiv data).symm.finiteDimensional

/-- Exact equality of the infinite-dimensional zero-mode count with the finite
Schur-kernel dimension. -/
theorem finiteModeSchur_operatorKernel_finrank_eq
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    Module.finrank Real operator.ker =
      Module.finrank Real data.schur.ker := by
  letI : FiniteDimensional Real data.schur.ker :=
    finiteModeSchurKernelFiniteDimensional data
  letI : FiniteDimensional Real operator.ker :=
    finiteModeSchurOperatorKernelFiniteDimensional data
  exact (finiteModeSchurKernelEquiv data).finrank_eq

/-- The number of actual zero modes is bounded by the number of selected
reference modes. -/
theorem finiteModeSchur_operatorKernel_finrank_le_card
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    Module.finrank Real operator.ker ≤ Fintype.card Mode := by
  letI : FiniteDimensional Real data.schur.ker :=
    finiteModeSchurKernelFiniteDimensional data
  letI : FiniteDimensional Real operator.ker :=
    finiteModeSchurOperatorKernelFiniteDimensional data
  calc
    Module.finrank Real operator.ker =
        Module.finrank Real data.schur.ker :=
      finiteModeSchur_operatorKernel_finrank_eq data
    _ ≤ Module.finrank Real (Mode → Real) :=
      Submodule.finrank_le data.schur.ker
    _ = Fintype.card Mode := by simp

/-- A canonical finite model whose coordinates are a chosen basis of the finite
Schur kernel, rather than a basis chosen directly in the full Hilbert space. -/
noncomputable def finiteModeSchurKernelModel
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    FiniteKernelModel operator := by
  letI : FiniteDimensional Real data.schur.ker :=
    finiteModeSchurKernelFiniteDimensional data
  exact
    { ZeroMode := Basis.ofVectorSpaceIndex Real data.schur.ker
      zeroModeFintype := Fintype.ofFinite _
      zeroModeDecidableEq := Classical.decEq _
      coordinates :=
        (Basis.ofVectorSpace Real data.schur.ker).equivFun.symm |>.trans
          (finiteModeSchurKernelEquiv data).symm }

/-- Public checkpoint for finite-mode elimination. -/
theorem finite_mode_schur_kernel_gate
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurKernelData operator Mode Complement) :
    Nonempty (operator.ker ≃ₗ[Real] data.schur.ker) ∧
      Module.finrank Real operator.ker ≤ Fintype.card Mode :=
  ⟨⟨finiteModeSchurKernelEquiv data⟩,
    finiteModeSchur_operatorKernel_finrank_le_card data⟩

end
end P0EFTJanusProgramPFiniteModeSchurKernel4D
end JanusFormal

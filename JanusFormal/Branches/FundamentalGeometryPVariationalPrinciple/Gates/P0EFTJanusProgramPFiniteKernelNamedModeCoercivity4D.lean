import Mathlib.LinearAlgebra.Basis.Fin
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelBasisCoercivity4D

/-!
# Named physical zero modes and coercivity

A basis indexed by an abstract finite type proves the right dimension, but the
final physical statement should also retain the actual ambient zero-mode
vectors.  This file stores a finite named family together with an exact
coordinate synthesis equivalence

`(ZeroMode → ℝ) ≃ₗ ker H`.

The coordinate vector supported at one label is required to synthesize to the
corresponding ambient mode.  Therefore the named vectors span exactly the real
kernel and have unique coefficients.  Mapping the standard basis through this
equivalence constructs the kernel basis consumed by the coercivity gate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModeCoercivity4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelBasisCoercivity4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Finite physical labels, their ambient vectors and an exact coordinate
synthesis onto the genuine operator kernel. -/
structure FiniteKernelNamedModeFamily
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  synthesis : (ZeroMode → Real) ≃ₗ[Real] operator.ker
  synthesis_single : ∀ mode,
    synthesis (Pi.single mode 1) =
      ⟨vector mode, annihilated mode⟩

/-- Kernel vector attached to one physical label. -/
def FiniteKernelNamedModeFamily.kernelVector
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (modes : FiniteKernelNamedModeFamily operator ZeroMode)
    (mode : ZeroMode) : operator.ker :=
  ⟨modes.vector mode, modes.annihilated mode⟩

/-- The named family canonically determines a basis of the actual kernel. -/
noncomputable def FiniteKernelNamedModeFamily.basis
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (modes : FiniteKernelNamedModeFamily operator ZeroMode) :
    Module.Basis ZeroMode Real operator.ker :=
  (Pi.basisFun Real ZeroMode).map modes.synthesis

@[simp]
theorem FiniteKernelNamedModeFamily.basis_apply
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (modes : FiniteKernelNamedModeFamily operator ZeroMode)
    (mode : ZeroMode) :
    modes.basis mode = modes.kernelVector mode := by
  classical
  simp [FiniteKernelNamedModeFamily.basis,
    FiniteKernelNamedModeFamily.kernelVector, modes.synthesis_single]

/-- Ambient linear synthesis of named zero modes. -/
def FiniteKernelNamedModeFamily.ambientSynthesis
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (modes : FiniteKernelNamedModeFamily operator ZeroMode) :
    (ZeroMode → Real) →ₗ[Real] E :=
  operator.ker.subtype.comp modes.synthesis.toLinearMap

@[simp]
theorem FiniteKernelNamedModeFamily.ambientSynthesis_single
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (modes : FiniteKernelNamedModeFamily operator ZeroMode)
    (mode : ZeroMode) :
    modes.ambientSynthesis (Pi.single mode 1) = modes.vector mode := by
  classical
  simp [FiniteKernelNamedModeFamily.ambientSynthesis,
    modes.synthesis_single]

/-- The range of ambient synthesis is exactly the true kernel viewed inside the
ambient space. -/
theorem FiniteKernelNamedModeFamily.ambientSynthesis_range
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (modes : FiniteKernelNamedModeFamily operator ZeroMode) :
    LinearMap.range modes.ambientSynthesis = operator.ker := by
  rw [FiniteKernelNamedModeFamily.ambientSynthesis]
  rw [LinearMap.range_comp]
  simp

/-- Named modes plus quadratic coercivity. -/
structure SelfAdjointNamedKernelCoercivityData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  modes : FiniteKernelNamedModeFamily operator ZeroMode
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ vector : SelfAdjointKernelComplement operator,
    constant * ‖(vector : E)‖ ^ 2 ≤
      ⟪(vector : E), operator (vector : E)⟫_Real

/-- Forget only the explicit ambient names and recover the basis/coercivity
packet used by the PDE-to-gap theorem. -/
def SelfAdjointNamedKernelCoercivityData.toBasisCoercivity
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointNamedKernelCoercivityData operator hSelfAdjoint ZeroMode) :
    SelfAdjointKernelBasisCoercivityData operator hSelfAdjoint ZeroMode where
  basis := data.modes.basis
  constant := data.constant
  constant_pos := data.constant_pos
  coercive := data.coercive

/-- Named modes construct the actual-kernel gap and retain the exact count. -/
theorem self_adjoint_named_kernel_coercivity_gate
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointNamedKernelCoercivityData operator hSelfAdjoint ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapData operator hSelfAdjoint) ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  self_adjoint_kernel_basis_coercivity_gate data.toBasisCoercivity

end
end P0EFTJanusProgramPFiniteKernelNamedModeCoercivity4D
end JanusFormal

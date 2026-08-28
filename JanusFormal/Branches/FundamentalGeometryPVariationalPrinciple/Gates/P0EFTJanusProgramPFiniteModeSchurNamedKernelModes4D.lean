import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModes4D

/-!
# Named actual zero modes from a basis of the finite Schur kernel

Finite-mode elimination already gives a canonical linear equivalence

`ker H ≃ ker S`.

The remaining finite computation should therefore be performed in `ker S`, not
by choosing a second basis directly in the ambient Hilbert space.  This file
accepts a physically named finite basis of the Schur kernel and transports it
back through the exact Schur reconstruction.  The resulting ambient vectors
are genuine zero modes of the original operator, span its complete kernel, and
have unique finite coordinates.

No projection, complementary kernel model or additional infinite-dimensional
choice is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurNamedKernelModes4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteModeSchurKernel4D
open P0EFTJanusProgramPFiniteKernelNamedModes4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- A physically labelled basis of the finite Schur kernel.  The infinite
operator kernel is reconstructed from it by the already proved Schur-kernel
equivalence. -/
structure FiniteModeSchurNamedKernelBasisData
    (operator : E →L[Real] E)
    (Mode Complement : Type*) (ZeroMode : Type)
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (schurData : FiniteModeSchurKernelData operator Mode Complement) where
  basis : Basis ZeroMode Real schurData.schur.ker

namespace FiniteModeSchurNamedKernelBasisData

variable {operator : E →L[Real] E}
variable {Mode Complement : Type*} {ZeroMode : Type}
variable [Fintype Mode] [DecidableEq Mode]
variable [AddCommGroup Complement] [Module Real Complement]
variable [Fintype ZeroMode] [DecidableEq ZeroMode]
variable {schurData : FiniteModeSchurKernelData operator Mode Complement}

/-- Exact finite coordinates of the actual operator kernel: first synthesize a
Schur-kernel vector in the supplied basis, then undo the Schur reduction. -/
noncomputable def coordinates
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData) :
    (ZeroMode → Real) ≃ₗ[Real] operator.ker :=
  named.basis.equivFun.symm.trans (finiteModeSchurKernelEquiv schurData).symm

/-- Ambient vector represented by one named coordinate axis. -/
noncomputable def vector
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData)
    (index : ZeroMode) : E :=
  (named.coordinates (finiteCoordinateUnit index)).1

/-- Every named vector is a genuine zero mode of the original operator. -/
theorem vector_mem_kernel
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData)
    (index : ZeroMode) :
    operator (named.vector index) = 0 :=
  (named.coordinates (finiteCoordinateUnit index)).2

/-- The supplied finite Schur basis produces the standard named-kernel packet
for the full operator. -/
noncomputable def toNamedModeFamily
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData) :
    FiniteKernelNamedModeFamily operator ZeroMode :=
  let actualCoordinates := named.coordinates
  { vector := fun index => (actualCoordinates (finiteCoordinateUnit index)).1
    vector_mem_kernel := fun index =>
      (actualCoordinates (finiteCoordinateUnit index)).2
    coordinates := actualCoordinates
    coordinates_unit := fun _ => rfl }

/-- Explicit synthesis formula: finite Schur coordinates are transported by
exact Gaussian reconstruction into the ambient kernel. -/
@[simp]
theorem synthesize_eq_schur_reconstruction
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData)
    (coefficient : ZeroMode → Real) :
    named.toNamedModeFamily.synthesize coefficient =
      ((finiteModeSchurKernelEquiv schurData).symm
        (named.basis.equivFun.symm coefficient)).1 :=
  rfl

/-- Analysis of an actual zero mode is exactly finite Schur-basis analysis
following the Schur-kernel equivalence. -/
@[simp]
theorem analyze_eq_schur_coordinates
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData)
    (zeroMode : operator.ker) :
    named.toNamedModeFamily.analyze zeroMode =
      named.basis.equivFun (finiteModeSchurKernelEquiv schurData zeroMode) :=
  rfl

/-- The named Schur modes span exactly the actual kernel and their number is
its exact dimension. -/
theorem kernel_finrank_eq_card
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData) :
    Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  named.toNamedModeFamily.kernel_finrank_eq_card

/-- The named zero-mode count is automatically bounded by the selected
reference-mode count. -/
theorem zeroMode_card_le_referenceMode_card
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData) :
    Fintype.card ZeroMode ≤ Fintype.card Mode := by
  rw [← named.kernel_finrank_eq_card]
  exact finiteModeSchur_operatorKernel_finrank_le_card schurData

/-- Public checkpoint: one finite basis of `ker S` yields concrete ambient zero
modes, exact synthesis and the complete zero-mode count of `H`. -/
theorem finite_mode_schur_named_kernel_modes_gate
    (named : FiniteModeSchurNamedKernelBasisData operator Mode Complement
      ZeroMode schurData) :
    Nonempty (FiniteKernelNamedModeFamily operator ZeroMode) ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode ∧
      Fintype.card ZeroMode ≤ Fintype.card Mode ∧
      (∀ index, operator (named.vector index) = 0) :=
  ⟨⟨named.toNamedModeFamily⟩, named.kernel_finrank_eq_card,
    named.zeroMode_card_le_referenceMode_card, named.vector_mem_kernel⟩

end FiniteModeSchurNamedKernelBasisData

end
end P0EFTJanusProgramPFiniteModeSchurNamedKernelModes4D
end JanusFormal

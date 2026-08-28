import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelModel4D

/-!
# Adapters from finite-dimensional kernels to finite coordinate models

An explicit physical classification of zero modes is preferable, but every
finite-dimensional kernel already admits a canonical chosen finite coordinate
model through `Basis.ofVectorSpace`.  This file supplies that compatibility
adapter.

The chosen basis is not asserted to have physical meaning.  It merely proves
that the classified-zero-mode interface is no stronger than the historical
finite-dimensional-kernel hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelModelAdapters4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteKernelModel4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Chosen finite coordinates on any finite-dimensional operator kernel. -/
noncomputable def finiteKernelModelOfFiniteDimensional
    (operator : E →L[Real] E)
    [FiniteDimensional Real operator.ker] :
    FiniteKernelModel operator where
  ZeroMode := Basis.ofVectorSpaceIndex Real operator.ker
  zeroModeFintype := Fintype.ofFinite _
  zeroModeDecidableEq := Classical.decEq _
  coordinates := (Basis.ofVectorSpace Real operator.ker).equivFun.symm

/-- The chosen model has exactly the actual kernel dimension. -/
theorem finiteKernelModelOfFiniteDimensional_finrank
    (operator : E →L[Real] E)
    [FiniteDimensional Real operator.ker] :
    Module.finrank Real operator.ker =
      Fintype.card
        (finiteKernelModelOfFiniteDimensional operator).ZeroMode := by
  let model := finiteKernelModelOfFiniteDimensional operator
  letI : Fintype model.ZeroMode := model.zeroModeFintype
  letI : DecidableEq model.ZeroMode := model.zeroModeDecidableEq
  exact model.kernel_finrank_eq_card

section Gap

variable [InnerProductSpace Real E] [CompleteSpace E]

/-- Add chosen finite coordinates to an existing actual-kernel gap packet. -/
noncomputable def selfAdjointKernelComplementGapWithChosenModel
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint := by
  letI : FiniteDimensional Real operator.ker := data.kernel_finite
  exact
    { model := finiteKernelModelOfFiniteDimensional operator
      gap := data.gap
      gap_pos := data.gap_pos
      lowerBound := data.lowerBound }

/-- Compatibility gate: an anonymous finite kernel plus a gap always yields a
finite coordinate model, without changing the analytic statement. -/
def actual_kernel_gap_to_chosen_finite_model_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint :=
  selfAdjointKernelComplementGapWithChosenModel operator hSelfAdjoint data

end Gap

end
end P0EFTJanusProgramPFiniteKernelModelAdapters4D
end JanusFormal

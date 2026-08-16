import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Norm control for the Riesz representative of a bounded bilinear form

For a real Hilbert space, the Riesz map is an isometry.  Therefore the bounded
operator representing a continuous bilinear form has operator norm bounded by
the bilinear-form norm.  This elementary estimate is the bridge from the H11
physical-form bound to the perturbative smallness condition used by H12.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRieszBilinearNorm4D

set_option autoImplicit false
noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Pointwise norm equality: Riesz representation changes no norm in the dual
slot. -/
theorem continuousLinearMapOfBilin_apply_norm_eq
    (form : E →L[Real] E →L[Real] Real)
    (vector : E) :
    ‖@InnerProductSpace.continuousLinearMapOfBilin Real E inferInstance
        inferInstance inferInstance inferInstance form vector‖ =
      ‖form vector‖ := by
  change
    ‖(InnerProductSpace.toDual Real E).symm (form vector)‖ = ‖form vector‖
  exact (InnerProductSpace.toDual Real E).symm.norm_map (form vector)

/-- The Riesz representative has operator norm at most the norm of the original
bounded bilinear form. -/
theorem continuousLinearMapOfBilin_opNorm_le
    (form : E →L[Real] E →L[Real] Real) :
    ‖@InnerProductSpace.continuousLinearMapOfBilin Real E inferInstance
        inferInstance inferInstance inferInstance form‖ ≤
      ‖form‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (norm_nonneg form)
  intro vector
  rw [continuousLinearMapOfBilin_apply_norm_eq form vector]
  exact form.le_opNorm vector

/-- Public Riesz norm checkpoint. -/
theorem riesz_bilinear_norm_gate
    (form : E →L[Real] E →L[Real] Real) :
    ‖@InnerProductSpace.continuousLinearMapOfBilin Real E inferInstance
        inferInstance inferInstance inferInstance form‖ ≤
      ‖form‖ :=
  continuousLinearMapOfBilin_opNorm_le form

end
end P0EFTJanusProgramPRieszBilinearNorm4D
end JanusFormal

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! A bounded square-zero increment gives an invertible shear. -/

namespace JanusFormal.P0EFTJanusProgramPT12NilpotentGraphShear4D

set_option autoImplicit false
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

def nilpotentShear (increment : E →L[Real] E)
    (hSquare : ∀ x, increment (increment x) = 0) : E ≃L[Real] E where
  toLinearEquiv :=
    { (ContinuousLinearMap.id Real E + increment).toLinearMap with
      invFun := fun x => x - increment x
      left_inv := by
        intro x
        change x + increment x - increment (x + increment x) = x
        rw [map_add, hSquare, add_zero, add_sub_cancel_right]
      right_inv := by
        intro x
        change x - increment x + increment (x - increment x) = x
        rw [map_sub, hSquare, sub_zero, sub_add_cancel] }
  continuous_toFun := (ContinuousLinearMap.id Real E + increment).continuous
  continuous_invFun := (ContinuousLinearMap.id Real E - increment).continuous

theorem nilpotentShear_apply (increment : E →L[Real] E)
    (hSquare : ∀ x, increment (increment x) = 0) (x : E) :
    nilpotentShear increment hSquare x = x + increment x := rfl

theorem nilpotentShear_symm_apply (increment : E →L[Real] E)
    (hSquare : ∀ x, increment (increment x) = 0) (x : E) :
    (nilpotentShear increment hSquare).symm x = x - increment x := rfl

/-- Invariance on generators extends to their closed linear span. -/
theorem topologicalClosure_invariant (increment : E →L[Real] E)
    (core : Submodule Real E) (hCore : ∀ x ∈ core, increment x ∈ core) :
    ∀ x ∈ core.topologicalClosure, increment x ∈ core.topologicalClosure := by
  have h : core.topologicalClosure ≤
      core.topologicalClosure.comap increment.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · intro x hx
      exact core.le_topologicalClosure (hCore x hx)
    · exact core.isClosed_topologicalClosure.preimage increment.continuous
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12NilpotentGraphShear4D


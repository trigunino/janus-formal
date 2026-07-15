import Mathlib

namespace JanusFormal.P0EFTJanusCompositeTwoLoopInsertion

set_option autoImplicit false

/-!
Conditional MS coefficients obtained by differentiating the validated mixed
sunset pole with respect to a source `J phi^2/2`.
-/

/-- The source pole `5 lambda6/(64 pi^2 epsilon)` and the engineering factor
four give the composite anomalous coefficient. -/
theorem conditional_non_ll_composite_anomalous_coefficient :
    4 * (5 / (64 * Real.pi ^ 2)) = 5 / (16 * Real.pi ^ 2) := by
  ring

/-- Combining the non-LL beta and composite anomalous coefficients leaves a
strictly positive Callan--Symanzik logarithmic coefficient. -/
theorem conditional_non_ll_callan_symanzik_coefficient :
    475 / (32 * Real.pi ^ 2) - 3 * (5 / (16 * Real.pi ^ 2)) =
      445 / (32 * Real.pi ^ 2) := by
  ring

theorem conditional_non_ll_callan_symanzik_positive :
    0 < 445 / (32 * Real.pi ^ 2) := by
  positivity

structure CompositeInsertionClosureStatus where
  sourceDeformationSpecified : Prop
  sunsetPoleDifferentiated : Prop
  additiveIdentityMixingSubtracted : Prop
  sourceOperatorConventionMatchedToCS : Prop
  llInsertionComputed : Prop

def compositeInsertionClosed (s : CompositeInsertionClosureStatus) : Prop :=
  s.sourceDeformationSpecified ∧
  s.sunsetPoleDifferentiated ∧
  s.additiveIdentityMixingSubtracted ∧
  s.sourceOperatorConventionMatchedToCS ∧
  s.llInsertionComputed

end JanusFormal.P0EFTJanusCompositeTwoLoopInsertion

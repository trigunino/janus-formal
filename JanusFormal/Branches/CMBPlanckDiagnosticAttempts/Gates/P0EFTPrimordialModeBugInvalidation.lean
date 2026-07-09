namespace JanusFormal
namespace P0EFTPrimordialModeBugInvalidation

set_option autoImplicit false

structure PrimordialModeBugInvalidation where
  zeroAmplitudeBugFound : Prop
  affectedRunsMarkedInvalid : Prop
  rerunRequiredBeforeCitation : Prop

def invalidationComplete (i : PrimordialModeBugInvalidation) : Prop :=
  i.zeroAmplitudeBugFound /\ i.affectedRunsMarkedInvalid /\ i.rerunRequiredBeforeCitation

theorem affected_runs_require_rerun
    (i : PrimordialModeBugInvalidation)
    (h : invalidationComplete i) :
    i.rerunRequiredBeforeCitation := by
  exact h.right.right

end P0EFTPrimordialModeBugInvalidation
end JanusFormal

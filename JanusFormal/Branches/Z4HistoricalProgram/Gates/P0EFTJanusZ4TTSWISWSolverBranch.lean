import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4TTSWISWDerivation

namespace JanusFormal
namespace P0EFTJanusZ4TTSWISWSolverBranch

set_option autoImplicit false

structure TTSWISWSolverBranch where
  derivedTTSourceIntegrated : Prop
  hiddenSWISWRegularizationIntegrated : Prop
  spectraExported : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def branchReady (b : TTSWISWSolverBranch) : Prop :=
  b.derivedTTSourceIntegrated /\
  b.hiddenSWISWRegularizationIntegrated /\
  b.spectraExported

theorem branch_uses_derived_tt_lowtt_terms
    (b : TTSWISWSolverBranch)
    (h : branchReady b) :
    b.derivedTTSourceIntegrated /\ b.hiddenSWISWRegularizationIntegrated := by
  exact And.intro h.left h.right.left

theorem branch_does_not_claim_planck
    (b : TTSWISWSolverBranch)
    (_h : branchReady b)
    (hNoClaim : Not b.planckValidationClaimed) :
    Not b.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4TTSWISWSolverBranch
end JanusFormal

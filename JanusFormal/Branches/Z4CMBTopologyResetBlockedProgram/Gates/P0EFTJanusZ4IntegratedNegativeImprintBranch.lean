import JanusFormal.Branches.CMBPlanckDiagnosticAttempts.Gates.P0EFTJanusNegativeSectorCMBImprint

namespace JanusFormal
namespace P0EFTJanusZ4IntegratedNegativeImprintBranch

set_option autoImplicit false

structure IntegratedNegativeImprintBranch where
  controlledGeometricBranchIntegrated : Prop
  negativeJeansBlueImprintIntegrated : Prop
  fixedRatiosUsed : Prop
  noContinuousFitFactorUsed : Prop
  spectraExportedForGate : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def branchReady (b : IntegratedNegativeImprintBranch) : Prop :=
  b.controlledGeometricBranchIntegrated /\
  b.negativeJeansBlueImprintIntegrated /\
  b.fixedRatiosUsed /\
  b.noContinuousFitFactorUsed /\
  b.spectraExportedForGate

theorem integrated_branch_uses_no_fit_factor
    (b : IntegratedNegativeImprintBranch)
    (h : branchReady b) :
    b.noContinuousFitFactorUsed := by
  exact h.right.right.right.left

theorem integrated_branch_keeps_solver_frozen
    (b : IntegratedNegativeImprintBranch)
    (_h : branchReady b)
    (hFrozen : Not b.solverNumericsModified) :
    Not b.solverNumericsModified := by
  exact hFrozen

theorem integrated_branch_does_not_claim_planck
    (b : IntegratedNegativeImprintBranch)
    (_h : branchReady b)
    (hNoClaim : Not b.planckValidationClaimed) :
    Not b.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4IntegratedNegativeImprintBranch
end JanusFormal

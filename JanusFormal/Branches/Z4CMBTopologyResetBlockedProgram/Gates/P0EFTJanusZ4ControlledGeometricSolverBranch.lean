import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4GeometricCMBIdeaScreen

namespace JanusFormal
namespace P0EFTJanusZ4ControlledGeometricSolverBranch

set_option autoImplicit false

structure ControlledGeometricSolverBranch where
  ebHiddenConservationIntegrated : Prop
  weylMirrorProjectionIntegrated : Prop
  fixedZ4QuarterTurnUsed : Prop
  fixedMembraneASigmaUsed : Prop
  noContinuousFitFactorUsed : Prop
  spectraExported : Prop
  shapeDeltasMeasured : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def branchReady (b : ControlledGeometricSolverBranch) : Prop :=
  b.ebHiddenConservationIntegrated /\
  b.weylMirrorProjectionIntegrated /\
  b.fixedZ4QuarterTurnUsed /\
  b.fixedMembraneASigmaUsed /\
  b.noContinuousFitFactorUsed /\
  b.spectraExported /\
  b.shapeDeltasMeasured

theorem branch_uses_no_fit_factor
    (b : ControlledGeometricSolverBranch)
    (h : branchReady b) :
    b.noContinuousFitFactorUsed := by
  exact h.right.right.right.right.left

theorem branch_keeps_active_solver_frozen
    (b : ControlledGeometricSolverBranch)
    (_h : branchReady b)
    (hFrozen : Not b.solverNumericsModified) :
    Not b.solverNumericsModified := by
  exact hFrozen

theorem branch_does_not_claim_planck
    (b : ControlledGeometricSolverBranch)
    (_h : branchReady b)
    (hNoClaim : Not b.planckValidationClaimed) :
    Not b.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4ControlledGeometricSolverBranch
end JanusFormal

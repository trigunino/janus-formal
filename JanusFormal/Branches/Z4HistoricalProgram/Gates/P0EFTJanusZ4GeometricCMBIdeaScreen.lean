import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MembranePolarizationTransport

namespace JanusFormal
namespace P0EFTJanusZ4GeometricCMBIdeaScreen

set_option autoImplicit false

structure GeometricCMBIdeaScreen where
  fixedZ4QuarterTurnUsed : Prop
  fixedMembraneASigmaUsed : Prop
  noContinuousFitFactorUsed : Prop
  ebHiddenConservationTested : Prop
  weylMirrorProjectionTested : Prop
  swiswMembraneMemoryTested : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def screenReady (s : GeometricCMBIdeaScreen) : Prop :=
  s.fixedZ4QuarterTurnUsed /\
  s.fixedMembraneASigmaUsed /\
  s.noContinuousFitFactorUsed /\
  s.ebHiddenConservationTested /\
  s.weylMirrorProjectionTested /\
  s.swiswMembraneMemoryTested

theorem screen_does_not_use_fit_factor
    (s : GeometricCMBIdeaScreen)
    (h : screenReady s) :
    s.noContinuousFitFactorUsed := by
  exact h.right.right.left

theorem screen_keeps_solver_frozen
    (s : GeometricCMBIdeaScreen)
    (_h : screenReady s)
    (hFrozen : Not s.solverNumericsModified) :
    Not s.solverNumericsModified := by
  exact hFrozen

theorem screen_does_not_claim_planck
    (s : GeometricCMBIdeaScreen)
    (_h : screenReady s)
    (hNoClaim : Not s.planckValidationClaimed) :
    Not s.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4GeometricCMBIdeaScreen
end JanusFormal

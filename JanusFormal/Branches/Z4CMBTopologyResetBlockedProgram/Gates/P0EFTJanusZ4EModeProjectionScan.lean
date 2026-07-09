import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4NativeTransferSolver

namespace JanusFormal
namespace P0EFTJanusZ4EModeProjectionScan

set_option autoImplicit false

structure EModeProjectionScan where
  nativeZ4SolverUsed : Prop
  compressedLCDMParametersNotUsed : Prop
  officialPlanckLikelihoodOptionallyExecuted : Prop
  spin2ProjectionScaleScanned : Prop
  activeScaleRestored : Prop
  singleNormalizationClosureNotClaimed : Prop
  fullPolarizationHierarchyStillRequired : Prop

def eModeProjectionScanReady (s : EModeProjectionScan) : Prop :=
  s.nativeZ4SolverUsed /\
  s.compressedLCDMParametersNotUsed /\
  s.officialPlanckLikelihoodOptionallyExecuted /\
  s.spin2ProjectionScaleScanned /\
  s.activeScaleRestored /\
  s.singleNormalizationClosureNotClaimed /\
  s.fullPolarizationHierarchyStillRequired

theorem emode_scan_preserves_active_solver_state
    (s : EModeProjectionScan)
    (h : eModeProjectionScanReady s) :
    s.activeScaleRestored := by
  exact h.right.right.right.right.left

theorem emode_scan_does_not_close_polarization_hierarchy
    (s : EModeProjectionScan)
    (h : eModeProjectionScanReady s) :
    s.fullPolarizationHierarchyStillRequired := by
  exact h.right.right.right.right.right.right

end P0EFTJanusZ4EModeProjectionScan
end JanusFormal

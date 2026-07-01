namespace JanusFormal
namespace P0EFTCMBPlanckBackgroundScan

set_option autoImplicit false

structure PlanckBackgroundScan where
  fullPlanckLikelihoodRun : Prop
  backgroundGridEvaluated : Prop
  bestPointRecorded : Prop
  bestPointAccepted : Prop

def backgroundScanReady (s : PlanckBackgroundScan) : Prop :=
  s.fullPlanckLikelihoodRun /\
  s.backgroundGridEvaluated /\
  s.bestPointRecorded

def backgroundScanAcceptsBranch (s : PlanckBackgroundScan) : Prop :=
  backgroundScanReady s /\
  s.bestPointAccepted

theorem background_scan_without_accepted_point_keeps_branch_rejected
    (s : PlanckBackgroundScan)
    (_hReady : backgroundScanReady s)
    (hRejected : Not s.bestPointAccepted) :
    Not (backgroundScanAcceptsBranch s) := by
  intro h
  exact hRejected h.right

end P0EFTCMBPlanckBackgroundScan
end JanusFormal

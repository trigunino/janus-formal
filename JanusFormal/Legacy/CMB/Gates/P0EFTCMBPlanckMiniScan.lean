namespace JanusFormal
namespace P0EFTCMBPlanckMiniScan

set_option autoImplicit false

structure PlanckMiniScan where
  fullPlanckLikelihoodRun : Prop
  finiteGridEvaluated : Prop
  bestPointRecorded : Prop
  bestPointAccepted : Prop

def miniScanReady (s : PlanckMiniScan) : Prop :=
  s.fullPlanckLikelihoodRun /\
  s.finiteGridEvaluated /\
  s.bestPointRecorded

def miniScanAcceptsBranch (s : PlanckMiniScan) : Prop :=
  miniScanReady s /\
  s.bestPointAccepted

theorem finite_scan_without_accepted_point_keeps_cmb_rejected
    (s : PlanckMiniScan)
    (_hReady : miniScanReady s)
    (hRejected : Not s.bestPointAccepted) :
    Not (miniScanAcceptsBranch s) := by
  intro h
  exact hRejected h.right

end P0EFTCMBPlanckMiniScan
end JanusFormal

namespace JanusFormal
namespace P0EFTImmirziPatchMiniScan

set_option autoImplicit false

structure ImmirziPatchMiniScan where
  gridRun : Prop
  bestPointFound : Prop
  planckAccepted : Prop

def miniScanDiagnosticReady (s : ImmirziPatchMiniScan) : Prop :=
  s.gridRun /\ s.bestPointFound

def miniScanNoFitReady (s : ImmirziPatchMiniScan) : Prop :=
  miniScanDiagnosticReady s /\ s.planckAccepted

theorem scan_without_planck_acceptance_blocks_no_fit
    (s : ImmirziPatchMiniScan)
    (hRun : s.gridRun)
    (hBest : s.bestPointFound)
    (hReject : Not s.planckAccepted) :
    miniScanDiagnosticReady s /\ Not (miniScanNoFitReady s) := by
  exact And.intro (And.intro hRun hBest) (by intro h; exact hReject h.right)

end P0EFTImmirziPatchMiniScan
end JanusFormal

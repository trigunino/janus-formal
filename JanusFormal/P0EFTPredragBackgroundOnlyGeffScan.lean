namespace JanusFormal
namespace P0EFTPredragBackgroundOnlyGeffScan

set_option autoImplicit false

structure PredragBackgroundOnlyGeffScan where
  backgroundOnlyGeffScanned : Prop
  perturbativeHolstStressDisabled : Prop
  soundHorizonProxyRecorded : Prop
  planckAccepted : Prop

def diagnosticReady (s : PredragBackgroundOnlyGeffScan) : Prop :=
  s.backgroundOnlyGeffScanned /\
  s.perturbativeHolstStressDisabled /\
  s.soundHorizonProxyRecorded

def cmbNoFitReady (s : PredragBackgroundOnlyGeffScan) : Prop :=
  diagnosticReady s /\ s.planckAccepted

theorem rejected_background_only_scan_blocks_no_fit
    (s : PredragBackgroundOnlyGeffScan)
    (hRejected : Not s.planckAccepted) :
    Not (cmbNoFitReady s) := by
  intro h
  exact hRejected h.right

end P0EFTPredragBackgroundOnlyGeffScan
end JanusFormal

namespace JanusFormal
namespace P0EFTLowETauRescueScan

set_option autoImplicit false

structure LowETauRescueScan where
  tauScanRun : Prop
  lowECanBeTuned : Prop
  highLStillRequiresPrimordialTransfer : Prop
  tauDerivedFromJanusGeometry : Prop
  primordialTransferDerived : Prop

def lowESectorConditionallyOpen (s : LowETauRescueScan) : Prop :=
  s.tauScanRun /\
  s.lowECanBeTuned

def cmbNoFitReadyAfterTauScan (s : LowETauRescueScan) : Prop :=
  lowESectorConditionallyOpen s /\
  s.tauDerivedFromJanusGeometry /\
  s.primordialTransferDerived

theorem tau_fit_is_not_geometry
    (s : LowETauRescueScan)
    (_hOpen : lowESectorConditionallyOpen s)
    (hMissing : Not s.tauDerivedFromJanusGeometry) :
    Not (cmbNoFitReadyAfterTauScan s) := by
  intro h
  exact hMissing h.right.left

theorem missing_primordial_transfer_still_blocks
    (s : LowETauRescueScan)
    (_hOpen : lowESectorConditionallyOpen s)
    (hMissing : Not s.primordialTransferDerived) :
    Not (cmbNoFitReadyAfterTauScan s) := by
  intro h
  exact hMissing h.right.right

end P0EFTLowETauRescueScan
end JanusFormal

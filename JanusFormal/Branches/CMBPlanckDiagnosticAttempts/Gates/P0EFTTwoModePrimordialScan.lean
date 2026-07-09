namespace JanusFormal
namespace P0EFTTwoModePrimordialScan

set_option autoImplicit false

structure TwoModePrimordialScan where
  preDragModeRun : Prop
  visibilityModeRun : Prop
  acceptedPointFound : Prop
  bothModesGeometricallyDerived : Prop

def twoModeWindowOpen (s : TwoModePrimordialScan) : Prop :=
  s.preDragModeRun /\
  s.visibilityModeRun /\
  s.acceptedPointFound

def twoModeNoFitReady (s : TwoModePrimordialScan) : Prop :=
  twoModeWindowOpen s /\
  s.bothModesGeometricallyDerived

theorem accepted_two_mode_still_needs_derivation
    (s : TwoModePrimordialScan)
    (_hOpen : twoModeWindowOpen s)
    (hMissing : Not s.bothModesGeometricallyDerived) :
    Not (twoModeNoFitReady s) := by
  intro h
  exact hMissing h.right

end P0EFTTwoModePrimordialScan
end JanusFormal

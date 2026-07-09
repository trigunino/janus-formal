namespace JanusFormal
namespace P0EFTWeylBalancedFineScan

set_option autoImplicit false

structure WeylBalancedFineScan where
  lensingSourceZero : Prop
  weylFineScanRun : Prop
  balancedDeltaWindowFound : Prop
  weylCoefficientGeometricallyDerived : Prop

def balancedWindowOpen (s : WeylBalancedFineScan) : Prop :=
  s.lensingSourceZero /\
  s.weylFineScanRun /\
  s.balancedDeltaWindowFound

def noFitBalancedWeylReady (s : WeylBalancedFineScan) : Prop :=
  balancedWindowOpen s /\
  s.weylCoefficientGeometricallyDerived

theorem balanced_window_still_needs_weyl_derivation
    (s : WeylBalancedFineScan)
    (_hOpen : balancedWindowOpen s)
    (hMissing : Not s.weylCoefficientGeometricallyDerived) :
    Not (noFitBalancedWeylReady s) := by
  intro h
  exact hMissing h.right

end P0EFTWeylBalancedFineScan
end JanusFormal

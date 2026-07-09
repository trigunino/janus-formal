namespace JanusFormal
namespace P0EFTScreenedRdCMBProjectionScan

set_option autoImplicit false

structure ScreenedRdCMBProjectionScan where
  fullBackgroundRdContraction : Prop
  screenedCMBEffectiveCoupling : Prop
  planckImprovingWindowFound : Prop
  screeningFactorDerived : Prop

def screenedWindowDiagnosticReady (s : ScreenedRdCMBProjectionScan) : Prop :=
  s.fullBackgroundRdContraction /\
  s.screenedCMBEffectiveCoupling /\
  s.planckImprovingWindowFound

def screenedNoFitReady (s : ScreenedRdCMBProjectionScan) : Prop :=
  screenedWindowDiagnosticReady s /\ s.screeningFactorDerived

theorem screening_window_still_requires_derivation
    (s : ScreenedRdCMBProjectionScan)
    (_hWindow : screenedWindowDiagnosticReady s)
    (hMissing : Not s.screeningFactorDerived) :
    Not (screenedNoFitReady s) := by
  intro h
  exact hMissing h.right

end P0EFTScreenedRdCMBProjectionScan
end JanusFormal

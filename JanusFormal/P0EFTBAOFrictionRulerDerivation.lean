namespace JanusFormal
namespace P0EFTBAOFrictionRulerDerivation

set_option autoImplicit false

structure BAOFrictionRulerDerivation where
  spinBackgroundScreened : Prop
  radialFrictionTargetApplied : Prop
  dvRulerFineScanPassed : Prop
  tauDragTargetEncoded : Prop
  tauDragDerivedFromHolstTransport : Prop

def baoFrictionRulerDiagnosticReady (d : BAOFrictionRulerDerivation) : Prop :=
  d.spinBackgroundScreened /\
  d.radialFrictionTargetApplied /\
  d.dvRulerFineScanPassed /\
  d.tauDragTargetEncoded

def baoFrictionRulerNoFitReady (d : BAOFrictionRulerDerivation) : Prop :=
  baoFrictionRulerDiagnosticReady d /\
  d.tauDragDerivedFromHolstTransport

theorem fine_scan_encodes_friction_ruler_target
    (d : BAOFrictionRulerDerivation)
    (hSpin : d.spinBackgroundScreened)
    (hRadial : d.radialFrictionTargetApplied)
    (hDV : d.dvRulerFineScanPassed)
    (hTau : d.tauDragTargetEncoded) :
    baoFrictionRulerDiagnosticReady d := by
  exact And.intro hSpin (And.intro hRadial (And.intro hDV hTau))

theorem missing_holst_transport_derivation_blocks_no_fit
    (d : BAOFrictionRulerDerivation)
    (hMissing : Not d.tauDragDerivedFromHolstTransport) :
    Not (baoFrictionRulerNoFitReady d) := by
  intro h
  exact hMissing h.right

end P0EFTBAOFrictionRulerDerivation
end JanusFormal

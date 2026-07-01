namespace JanusFormal
namespace P0EFTDESIBAOFinalHolstGate

set_option autoImplicit false

structure DESIBAOFinalHolstGate where
  spinBackgroundScreened : Prop
  radialPhotonTransportApplied : Prop
  holstPlasmaSoundRulerDerived : Prop
  desiBAOShapeGatePassed : Prop
  directCMBTransferFunctionsDerived : Prop

def desiBAONoFitDiagnosticReady (g : DESIBAOFinalHolstGate) : Prop :=
  g.spinBackgroundScreened /\
  g.radialPhotonTransportApplied /\
  g.holstPlasmaSoundRulerDerived /\
  g.desiBAOShapeGatePassed

def fullDirectCMBReady (g : DESIBAOFinalHolstGate) : Prop :=
  desiBAONoFitDiagnosticReady g /\
  g.directCMBTransferFunctionsDerived

theorem desi_bao_gate_closes_with_holst_plasma_ruler
    (g : DESIBAOFinalHolstGate)
    (hSpin : g.spinBackgroundScreened)
    (hRadial : g.radialPhotonTransportApplied)
    (hRuler : g.holstPlasmaSoundRulerDerived)
    (hBAO : g.desiBAOShapeGatePassed) :
    desiBAONoFitDiagnosticReady g := by
  exact And.intro hSpin (And.intro hRadial (And.intro hRuler hBAO))

theorem missing_direct_cmb_transfer_keeps_cmb_open
    (g : DESIBAOFinalHolstGate)
    (hMissing : Not g.directCMBTransferFunctionsDerived) :
    Not (fullDirectCMBReady g) := by
  intro h
  exact hMissing h.right

end P0EFTDESIBAOFinalHolstGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusRP4PinSignAuditGate

set_option autoImplicit false

structure RP4PinSignAuditGate where
  globalBaseIsRP4 : Prop
  rp4NonOrientableRecorded : Prop
  rp2BoyShadowNotUsedAsGlobalPinProof : Prop
  pinSignComputedForRP4 : Prop
  rp4BasePinPlusExists : Prop
  rp4BasePinMinusExists : Prop
  sigmaApsBoundaryPinLiftClosed : Prop
  pinMinusLiftAllowed : Prop
  apsPinClosureAllowed : Prop

def rp4PinBaseComputedButSigmaApsOpen (g : RP4PinSignAuditGate) : Prop :=
  g.globalBaseIsRP4 /\
  g.rp4NonOrientableRecorded /\
  g.rp2BoyShadowNotUsedAsGlobalPinProof /\
  g.pinSignComputedForRP4 /\
  g.rp4BasePinPlusExists /\
  Not g.rp4BasePinMinusExists /\
  Not g.sigmaApsBoundaryPinLiftClosed /\
  Not g.pinMinusLiftAllowed /\
  Not g.apsPinClosureAllowed

theorem sigma_aps_pin_lift_still_blocks_aps_pin_closure
    (g : RP4PinSignAuditGate)
    (h : rp4PinBaseComputedButSigmaApsOpen g) :
    Not g.apsPinClosureAllowed := by
  exact h.2.2.2.2.2.2.2.2

end P0EFTJanusRP4PinSignAuditGate
end JanusFormal

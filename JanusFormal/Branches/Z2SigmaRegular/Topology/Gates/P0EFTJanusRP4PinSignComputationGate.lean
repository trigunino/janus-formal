namespace JanusFormal
namespace P0EFTJanusRP4PinSignComputationGate

set_option autoImplicit false

structure RP4PinSignComputationGate where
  tangentStiefelWhitneyFormulaApplied : Prop
  w1Nonzero : Prop
  w2Zero : Prop
  w1SquaredNonzero : Prop
  rp4PinPlusExists : Prop
  rp4PinMinusExists : Prop
  sigmaApsBoundaryPinLiftClosed : Prop

def rp4BasePinSignComputed (g : RP4PinSignComputationGate) : Prop :=
  g.tangentStiefelWhitneyFormulaApplied /\
  g.w1Nonzero /\
  g.w2Zero /\
  g.w1SquaredNonzero /\
  g.rp4PinPlusExists /\
  Not g.rp4PinMinusExists

def rp4BaseComputedSigmaApsOpen (g : RP4PinSignComputationGate) : Prop :=
  rp4BasePinSignComputed g /\
  Not g.sigmaApsBoundaryPinLiftClosed

theorem rp4_pin_minus_obstructed_by_w1_square
    (g : RP4PinSignComputationGate)
    (h : rp4BasePinSignComputed g) :
    Not g.rp4PinMinusExists := by
  exact h.2.2.2.2.2

theorem rp4_base_result_does_not_close_sigma_aps
    (g : RP4PinSignComputationGate)
    (h : rp4BaseComputedSigmaApsOpen g) :
    Not g.sigmaApsBoundaryPinLiftClosed := by
  exact h.2

end P0EFTJanusRP4PinSignComputationGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusSigmaAPSPinLiftObligationGate

set_option autoImplicit false

structure SigmaAPSPinLiftObligationGate where
  sigmaBoundaryDefined : Prop
  rp4BasePinPlusComputed : Prop
  rp4BasePinMinusObstructed : Prop
  sigmaInducedPinStructureDeclared : Prop
  apsBoundaryProjectorDeclared : Prop
  fredholmDomainDeclared : Prop
  etaZeroModeCancellationDeclared : Prop
  parityAnomalyCancellationDeclared : Prop
  sigmaApsBoundaryPinLiftClosed : Prop
  apsPinClosureAllowed : Prop

def sigmaApsPinLiftObligationsDeclared
    (g : SigmaAPSPinLiftObligationGate) : Prop :=
  g.sigmaBoundaryDefined /\
  g.rp4BasePinPlusComputed /\
  g.rp4BasePinMinusObstructed /\
  g.sigmaInducedPinStructureDeclared /\
  g.apsBoundaryProjectorDeclared /\
  g.fredholmDomainDeclared /\
  g.etaZeroModeCancellationDeclared /\
  g.parityAnomalyCancellationDeclared

def sigmaApsPinLiftStillOpen
    (g : SigmaAPSPinLiftObligationGate) : Prop :=
  sigmaApsPinLiftObligationsDeclared g /\
  Not g.sigmaApsBoundaryPinLiftClosed /\
  Not g.apsPinClosureAllowed

theorem sigma_aps_pin_lift_required_for_aps_closure
    (g : SigmaAPSPinLiftObligationGate)
    (h : sigmaApsPinLiftStillOpen g) :
    Not g.apsPinClosureAllowed := by
  exact h.2.2

theorem rp4_pin_plus_alone_does_not_close_sigma_aps
    (g : SigmaAPSPinLiftObligationGate)
    (h : sigmaApsPinLiftStillOpen g) :
    g.rp4BasePinPlusComputed /\ Not g.sigmaApsBoundaryPinLiftClosed := by
  exact And.intro h.1.2.1 h.2.1

end P0EFTJanusSigmaAPSPinLiftObligationGate
end JanusFormal

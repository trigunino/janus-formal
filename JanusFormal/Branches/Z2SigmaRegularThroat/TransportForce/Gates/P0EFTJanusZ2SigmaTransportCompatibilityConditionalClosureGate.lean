import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaTransportCompatibilitySourceEquationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaSameSectorStressConservationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTransportCompatibilityConditionalClosureGate

set_option autoImplicit false

structure TransportCompatibilityConditionalClosureGate where
  sourceEquationGateImported : Prop
  sameSectorStressConservationGateImported : Prop
  sameSectorPlusStressConserved : Prop
  sameSectorMinusStressConserved : Prop
  transportedMinusContinuityDerived : Prop
  transportedPlusContinuityDerived : Prop
  minusToPlusConnectionForceCancellationDerived : Prop
  plusToMinusConnectionForceCancellationDerived : Prop
  sameBridgeForStressAndOptics : Prop
  plusTransportCompatibilitySourceDerived : Prop
  minusTransportCompatibilitySourceDerived : Prop

def conditionalClosureHypothesesReady
    (g : TransportCompatibilityConditionalClosureGate) : Prop :=
  g.sourceEquationGateImported /\
  g.sameSectorStressConservationGateImported /\
  g.sameSectorPlusStressConserved /\
  g.sameSectorMinusStressConserved /\
  g.transportedMinusContinuityDerived /\
  g.transportedPlusContinuityDerived /\
  g.minusToPlusConnectionForceCancellationDerived /\
  g.plusToMinusConnectionForceCancellationDerived /\
  g.sameBridgeForStressAndOptics

def conditionalCompatibilityReady
    (g : TransportCompatibilityConditionalClosureGate) : Prop :=
  conditionalClosureHypothesesReady g /\
  g.plusTransportCompatibilitySourceDerived /\
  g.minusTransportCompatibilitySourceDerived

theorem conditional_closure_feeds_both_transport_compatibilities
    (g : TransportCompatibilityConditionalClosureGate)
    (hReady : conditionalCompatibilityReady g) :
    g.plusTransportCompatibilitySourceDerived /\
      g.minusTransportCompatibilitySourceDerived := by
  exact And.intro hReady.right.left hReady.right.right

theorem missing_minus_to_plus_force_blocks_conditional_closure
    (g : TransportCompatibilityConditionalClosureGate)
    (hMissing : Not g.minusToPlusConnectionForceCancellationDerived) :
    Not (conditionalCompatibilityReady g) := by
  intro hReady
  exact hMissing hReady.left.right.right.right.right.right.right.left

theorem missing_plus_to_minus_force_blocks_conditional_closure
    (g : TransportCompatibilityConditionalClosureGate)
    (hMissing : Not g.plusToMinusConnectionForceCancellationDerived) :
    Not (conditionalCompatibilityReady g) := by
  intro hReady
  exact hMissing hReady.left.right.right.right.right.right.right.right.left

end P0EFTJanusZ2SigmaTransportCompatibilityConditionalClosureGate
end JanusFormal

import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusPTNormalToSym4InternalMatrixAttemptGate

namespace JanusFormal
namespace P0EFTJanusNormalConnectionToSym4AnormalBridgeGate

set_option autoImplicit false

structure NormalConnectionToSym4AnormalBridgeGate where
  normalConnectionCalculatorReady : Prop
  activeNormalFramePrimitivesMaterialized : Prop
  omegaPerpActiveReady : Prop
  rhoPerpToEndC11Derived : Prop
  ANormalOnC11Defined : Prop
  ANormalLiftToSym4Defined : Prop
  ANormalOrders1001States : Prop

def normalConnectionToSym4Closed
    (g : NormalConnectionToSym4AnormalBridgeGate) : Prop :=
  g.normalConnectionCalculatorReady /\
  g.activeNormalFramePrimitivesMaterialized /\
  g.omegaPerpActiveReady /\
  g.rhoPerpToEndC11Derived /\
  g.ANormalOnC11Defined /\
  g.ANormalLiftToSym4Defined /\
  g.ANormalOrders1001States

def normalConnectionToSym4Frontier
    (g : NormalConnectionToSym4AnormalBridgeGate) : Prop :=
  g.normalConnectionCalculatorReady /\
  Not g.activeNormalFramePrimitivesMaterialized /\
  Not g.rhoPerpToEndC11Derived /\
  Not g.ANormalOnC11Defined

theorem normal_connection_without_rho_perp_blocks_A_normal
    (g : NormalConnectionToSym4AnormalBridgeGate)
    (hFrontier : normalConnectionToSym4Frontier g) :
    Not (normalConnectionToSym4Closed g) := by
  intro h
  exact hFrontier.2.2.1 h.2.2.2.1

end P0EFTJanusNormalConnectionToSym4AnormalBridgeGate
end JanusFormal

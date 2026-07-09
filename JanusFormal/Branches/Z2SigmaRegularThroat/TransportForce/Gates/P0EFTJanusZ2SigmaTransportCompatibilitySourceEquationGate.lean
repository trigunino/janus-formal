import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaTransportMapDerivationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTransportCompatibilitySourceEquationGate

set_option autoImplicit false

structure TransportCompatibilitySourceEquationGate where
  transportMapDerivationGateImported : Prop
  plusEffectiveRhsDeclared : Prop
  minusEffectiveRhsDeclared : Prop
  plusCovariantDivergenceEquationDeclared : Prop
  minusCovariantDivergenceEquationDeclared : Prop
  sameBridgeUsedInBothDivergences : Prop
  determinantFactorsKeptOutsideBridge : Prop
  activeMatterSourceEquationsRequired : Prop
  plusSourceDivergenceEquationDerived : Prop
  minusSourceDivergenceEquationDerived : Prop
  plusTransportCompatibilitySourceDerived : Prop
  minusTransportCompatibilitySourceDerived : Prop

def compatibilitySourceEquationLedgerDeclared
    (g : TransportCompatibilitySourceEquationGate) : Prop :=
  g.transportMapDerivationGateImported /\
  g.plusEffectiveRhsDeclared /\
  g.minusEffectiveRhsDeclared /\
  g.plusCovariantDivergenceEquationDeclared /\
  g.minusCovariantDivergenceEquationDeclared /\
  g.sameBridgeUsedInBothDivergences /\
  g.determinantFactorsKeptOutsideBridge /\
  g.activeMatterSourceEquationsRequired

def compatibilitySourceEquationReady
    (g : TransportCompatibilitySourceEquationGate) : Prop :=
  compatibilitySourceEquationLedgerDeclared g /\
  g.plusSourceDivergenceEquationDerived /\
  g.minusSourceDivergenceEquationDerived /\
  g.plusTransportCompatibilitySourceDerived /\
  g.minusTransportCompatibilitySourceDerived

theorem source_equations_feed_transport_compatibility
    (g : TransportCompatibilitySourceEquationGate)
    (hReady : compatibilitySourceEquationReady g) :
    g.plusTransportCompatibilitySourceDerived /\
      g.minusTransportCompatibilitySourceDerived := by
  exact And.intro hReady.right.right.right.left hReady.right.right.right.right

theorem missing_plus_source_divergence_blocks_compatibility_ready
    (g : TransportCompatibilitySourceEquationGate)
    (hMissing : Not g.plusSourceDivergenceEquationDerived) :
    Not (compatibilitySourceEquationReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem missing_minus_source_divergence_blocks_compatibility_ready
    (g : TransportCompatibilitySourceEquationGate)
    (hMissing : Not g.minusSourceDivergenceEquationDerived) :
    Not (compatibilitySourceEquationReady g) := by
  intro hReady
  exact hMissing hReady.right.right.left

end P0EFTJanusZ2SigmaTransportCompatibilitySourceEquationGate
end JanusFormal

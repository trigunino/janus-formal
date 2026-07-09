namespace JanusFormal
namespace P0EFTJanusCrosscapPTTransitionObstructionGate

set_option autoImplicit false

structure CrosscapPTTransitionObstructionGate where
  SigmaRadiusRemoved : Prop
  NonorientablePTTransitionDeclared : Prop
  TopologicalZ2ActionAvailable : Prop
  LocalFieldEquationsOnCrosscapDerived : Prop
  StressFreeTransitionProved : Prop
  RedshiftClockLawDerived : Prop
  RulerContractDerived : Prop

def CrosscapPTTransitionClosed
    (g : CrosscapPTTransitionObstructionGate) : Prop :=
  g.SigmaRadiusRemoved /\
  g.NonorientablePTTransitionDeclared /\
  g.TopologicalZ2ActionAvailable /\
  g.LocalFieldEquationsOnCrosscapDerived /\
  g.StressFreeTransitionProved /\
  g.RedshiftClockLawDerived /\
  g.RulerContractDerived

def CrosscapPTTransitionFrontier
    (g : CrosscapPTTransitionObstructionGate) : Prop :=
  g.SigmaRadiusRemoved /\
  g.NonorientablePTTransitionDeclared /\
  g.TopologicalZ2ActionAvailable /\
  Not g.LocalFieldEquationsOnCrosscapDerived /\
  Not g.StressFreeTransitionProved /\
  Not g.RedshiftClockLawDerived /\
  Not g.RulerContractDerived

theorem crosscap_topology_alone_does_not_close_dynamics
    (g : CrosscapPTTransitionObstructionGate)
    (hFrontier : CrosscapPTTransitionFrontier g) :
    Not (CrosscapPTTransitionClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusCrosscapPTTransitionObstructionGate
end JanusFormal

import JanusFormal.Legacy.P0EFT.Gates.P0EFTOrbifoldSingularCycleGenerator
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusProjectiveTunnelInterface

namespace JanusFormal
namespace P0EFTJanusAroundSigmaZ2CycleTransportGate

set_option autoImplicit false

structure AroundSigmaZ2CycleTransportGate where
  tunnelThroatSigmaDefined : Prop
  aroundSigmaCycleDefined : Prop
  quotientProjectionToZ2Defined : Prop
  aroundSigmaMapsToZ2Generator : Prop
  cyclicZ4MonodromyRequired : Prop
  transportClosed : Prop

def aroundSigmaZ2TransportClosed
    (g : AroundSigmaZ2CycleTransportGate) : Prop :=
  g.tunnelThroatSigmaDefined /\
  g.aroundSigmaCycleDefined /\
  g.quotientProjectionToZ2Defined /\
  g.aroundSigmaMapsToZ2Generator /\
  Not g.cyclicZ4MonodromyRequired /\
  g.transportClosed

theorem around_sigma_transport_supplies_z2_generator
    (g : AroundSigmaZ2CycleTransportGate)
    (h : aroundSigmaZ2TransportClosed g) :
    P0EFTOrbifoldSingularCycleGenerator.singularCycleRepresentsGeneratorDerived
      { singularCycleAroundSigmaDefined := g.aroundSigmaCycleDefined
        quotientProjectionToZ2Defined := g.quotientProjectionToZ2Defined
        aroundSigmaMapsToGenerator := g.aroundSigmaMapsToZ2Generator } := by
  unfold aroundSigmaZ2TransportClosed at h
  unfold P0EFTOrbifoldSingularCycleGenerator.singularCycleRepresentsGeneratorDerived
  exact And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1)

theorem around_sigma_z2_transport_does_not_require_cyclic_z4
    (g : AroundSigmaZ2CycleTransportGate)
    (h : aroundSigmaZ2TransportClosed g) :
    Not g.cyclicZ4MonodromyRequired := by
  exact h.2.2.2.2.1

end P0EFTJanusAroundSigmaZ2CycleTransportGate
end JanusFormal

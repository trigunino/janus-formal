import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldSingularCycleGenerator

namespace JanusFormal
namespace P0EFTJanusZ2TunnelCoreGate

set_option autoImplicit false

structure JanusZ2TunnelCore where
  projectiveTunnelClosed : Prop
  throatSigmaDefined : Prop
  aroundSigmaCycleDefined : Prop
  aroundSigmaMapsToZ2Generator : Prop
  z2CoverIsActiveGeometry : Prop
  fourSectorsAreProductZ2xZ2 : Prop
  cyclicZ4Required : Prop
  z4CMBMarkedNonEvidence : Prop

def z2TunnelCoreClosed (c : JanusZ2TunnelCore) : Prop :=
  c.projectiveTunnelClosed /\
  c.throatSigmaDefined /\
  c.aroundSigmaCycleDefined /\
  c.aroundSigmaMapsToZ2Generator /\
  c.z2CoverIsActiveGeometry /\
  c.fourSectorsAreProductZ2xZ2 /\
  Not c.cyclicZ4Required /\
  c.z4CMBMarkedNonEvidence

theorem z2_tunnel_core_needs_no_cyclic_z4
    (c : JanusZ2TunnelCore)
    (h : z2TunnelCoreClosed c) :
    c.z2CoverIsActiveGeometry /\ Not c.cyclicZ4Required := by
  exact And.intro h.2.2.2.2.1 h.2.2.2.2.2.2.1

theorem z2_tunnel_core_supplies_cycle_transport
    (c : JanusZ2TunnelCore)
    (h : z2TunnelCoreClosed c) :
    P0EFTOrbifoldSingularCycleGenerator.singularCycleRepresentsGeneratorDerived
      { singularCycleAroundSigmaDefined := c.aroundSigmaCycleDefined
        quotientProjectionToZ2Defined := c.z2CoverIsActiveGeometry
        aroundSigmaMapsToGenerator := c.aroundSigmaMapsToZ2Generator } := by
  unfold P0EFTOrbifoldSingularCycleGenerator.singularCycleRepresentsGeneratorDerived
  exact And.intro h.2.2.1 (And.intro h.2.2.2.2.1 h.2.2.2.1)

end P0EFTJanusZ2TunnelCoreGate
end JanusFormal

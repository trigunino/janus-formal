import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusAnormalSym4SpectralConditionGate

namespace JanusFormal
namespace P0EFTJanusQuantumFockNoCarryANormalCandidateGate

set_option autoImplicit false

structure QuantumFockNoCarryANormalCandidateGate where
  Sym4FockOccupationSectorDeclared : Prop
  NoCarryBaseEqualsDegreePlusOne : Prop
  ANoCarryOrdersAll1001States : Prop
  OrderedC11ModeBasisJanusDerived : Prop
  NoCarryModularHamiltonianJanusDerived : Prop
  RhoPerpMapsToANoCarry : Prop

def QuantumFockNoCarryClosed
    (g : QuantumFockNoCarryANormalCandidateGate) : Prop :=
  g.Sym4FockOccupationSectorDeclared /\
  g.NoCarryBaseEqualsDegreePlusOne /\
  g.ANoCarryOrdersAll1001States /\
  g.OrderedC11ModeBasisJanusDerived /\
  g.NoCarryModularHamiltonianJanusDerived /\
  g.RhoPerpMapsToANoCarry

def QuantumFockNoCarryFrontier
    (g : QuantumFockNoCarryANormalCandidateGate) : Prop :=
  g.Sym4FockOccupationSectorDeclared /\
  g.NoCarryBaseEqualsDegreePlusOne /\
  g.ANoCarryOrdersAll1001States /\
  Not g.OrderedC11ModeBasisJanusDerived /\
  Not g.NoCarryModularHamiltonianJanusDerived /\
  Not g.RhoPerpMapsToANoCarry

theorem exact_ordering_is_not_yet_janus_derivation
    (g : QuantumFockNoCarryANormalCandidateGate)
    (hFrontier : QuantumFockNoCarryFrontier g) :
    Not (QuantumFockNoCarryClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusQuantumFockNoCarryANormalCandidateGate
end JanusFormal

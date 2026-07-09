import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusQuantumFockNoCarryANormalCandidateGate

namespace JanusFormal
namespace P0EFTJanusSouriauTorsorC11NoCarryBridgeGate

set_option autoImplicit false

structure SouriauTorsorC11NoCarryBridgeGate where
  TorsorComponentsLGPEQDeclared : Prop
  TorsorDimensionEquals11 : Prop
  C11BasisAnchoredInTorsor : Prop
  CanonicalBlockFiltrationAvailable : Prop
  CanonicalComponentOrderDerived : Prop
  BaseFiveHierarchyDerivedFromGroupAction : Prop

def SouriauTorsorNoCarryClosed
    (g : SouriauTorsorC11NoCarryBridgeGate) : Prop :=
  g.TorsorDimensionEquals11 /\
  g.C11BasisAnchoredInTorsor /\
  g.CanonicalComponentOrderDerived /\
  g.BaseFiveHierarchyDerivedFromGroupAction

def SouriauTorsorNoCarryFrontier
    (g : SouriauTorsorC11NoCarryBridgeGate) : Prop :=
  g.TorsorComponentsLGPEQDeclared /\
  g.TorsorDimensionEquals11 /\
  g.C11BasisAnchoredInTorsor /\
  g.CanonicalBlockFiltrationAvailable /\
  Not g.CanonicalComponentOrderDerived /\
  Not g.BaseFiveHierarchyDerivedFromGroupAction

theorem c11_anchor_without_order_does_not_close_nocarry
    (g : SouriauTorsorC11NoCarryBridgeGate)
    (hFrontier : SouriauTorsorNoCarryFrontier g) :
    Not (SouriauTorsorNoCarryClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.1 h.2.2.1

end P0EFTJanusSouriauTorsorC11NoCarryBridgeGate
end JanusFormal

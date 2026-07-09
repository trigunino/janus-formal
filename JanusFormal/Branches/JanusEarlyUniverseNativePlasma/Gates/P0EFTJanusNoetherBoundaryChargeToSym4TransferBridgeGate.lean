import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusNormalRedshiftHamiltonianRouteMatrixGate

namespace JanusFormal
namespace P0EFTJanusNoetherBoundaryChargeToSym4TransferBridgeGate

set_option autoImplicit false

structure NoetherBoundaryChargeToSym4TransferBridgeGate where
  covariantPhaseSpaceFormulaDeclared : Prop
  symbolicBoundaryHamiltonianReady : Prop
  numericBoundaryHamiltonianReady : Prop
  boundaryHUsedAsNormalGenerator : Prop
  boundaryHMapsToEndSym4C11 : Prop
  Z2PTCovarianceProved : Prop
  ordered1001SpectrumProved : Prop
  photonDragUsesSameClock : Prop

def NoetherSym4BridgeClosed
    (g : NoetherBoundaryChargeToSym4TransferBridgeGate) : Prop :=
  g.covariantPhaseSpaceFormulaDeclared /\
  g.symbolicBoundaryHamiltonianReady /\
  g.numericBoundaryHamiltonianReady /\
  g.boundaryHUsedAsNormalGenerator /\
  g.boundaryHMapsToEndSym4C11 /\
  g.Z2PTCovarianceProved /\
  g.ordered1001SpectrumProved /\
  g.photonDragUsesSameClock

def NoetherSym4BridgeFrontier
    (g : NoetherBoundaryChargeToSym4TransferBridgeGate) : Prop :=
  g.covariantPhaseSpaceFormulaDeclared /\
  g.symbolicBoundaryHamiltonianReady /\
  Not g.numericBoundaryHamiltonianReady /\
  Not g.boundaryHUsedAsNormalGenerator /\
  Not g.boundaryHMapsToEndSym4C11 /\
  Not g.ordered1001SpectrumProved

theorem symbolic_boundary_hamiltonian_without_sym4_map_blocks_bridge
    (g : NoetherBoundaryChargeToSym4TransferBridgeGate)
    (hFrontier : NoetherSym4BridgeFrontier g) :
    Not (NoetherSym4BridgeClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.1 h.2.2.2.2.1

end P0EFTJanusNoetherBoundaryChargeToSym4TransferBridgeGate
end JanusFormal

import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusNoetherBoundaryChargeToSym4TransferBridgeGate

namespace JanusFormal
namespace P0EFTJanusBoundaryHamiltonianScalarVsOperatorAuditGate

set_option autoImplicit false

structure BoundaryHamiltonianScalarVsOperatorAuditGate where
  scalarBoundaryEnergyAvailable : Prop
  scalarBoundaryEnergyActsAsIdentityOnSym4 : Prop
  scalarBoundaryEnergyOrders1001States : Prop
  M31ValuedBoundaryChargeAvailable : Prop
  nonDiagonalBoundaryTransferAvailable : Prop
  operatorValuedBoundaryHamiltonianAvailable : Prop
  ordered1001SpectrumProved : Prop

def boundaryHamiltonianOperatorClosed
    (g : BoundaryHamiltonianScalarVsOperatorAuditGate) : Prop :=
  g.scalarBoundaryEnergyAvailable /\
  (
    g.M31ValuedBoundaryChargeAvailable \/
    g.nonDiagonalBoundaryTransferAvailable \/
    g.operatorValuedBoundaryHamiltonianAvailable
  ) /\
  g.ordered1001SpectrumProved

def boundaryHamiltonianOperatorFrontier
    (g : BoundaryHamiltonianScalarVsOperatorAuditGate) : Prop :=
  g.scalarBoundaryEnergyAvailable /\
  g.scalarBoundaryEnergyActsAsIdentityOnSym4 /\
  Not g.scalarBoundaryEnergyOrders1001States /\
  Not g.M31ValuedBoundaryChargeAvailable /\
  Not g.nonDiagonalBoundaryTransferAvailable /\
  Not g.operatorValuedBoundaryHamiltonianAvailable /\
  Not g.ordered1001SpectrumProved

theorem scalar_boundary_hamiltonian_cannot_close_sym4_transfer
    (g : BoundaryHamiltonianScalarVsOperatorAuditGate)
    (hFrontier : boundaryHamiltonianOperatorFrontier g) :
    Not (boundaryHamiltonianOperatorClosed g) := by
  intro h
  rcases h.2.1 with hM31 | hNonDiag | hOperator
  · exact hFrontier.2.2.2.1 hM31
  · exact hFrontier.2.2.2.2.1 hNonDiag
  · exact hFrontier.2.2.2.2.2.1 hOperator

end P0EFTJanusBoundaryHamiltonianScalarVsOperatorAuditGate
end JanusFormal

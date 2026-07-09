import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSym4TransferGeneratorCandidateMatrixGate

namespace JanusFormal
namespace P0EFTJanusSym4DiagonalHamiltonianOrderingAuditGate

set_option autoImplicit false

structure Sym4DiagonalHamiltonianOrderingAuditGate where
  HilbertDimensionEquals1001 : Prop
  M31PhysicalBlocksAreEllGPEQ : Prop
  isotropicBlockProfilesEqual70 : Prop
  isotropicBlockWeightsOrderAll1001States : Prop
  componentwiseWeightsBreakIsotropyOrNeedSelector : Prop
  genericWeightsRustineWithoutJanusOrigin : Prop
  extraSelectorDerived : Prop

def diagonalHamiltonianOrderingClosed
    (g : Sym4DiagonalHamiltonianOrderingAuditGate) : Prop :=
  g.HilbertDimensionEquals1001 /\
  g.M31PhysicalBlocksAreEllGPEQ /\
  (
    g.isotropicBlockWeightsOrderAll1001States \/
    (g.componentwiseWeightsBreakIsotropyOrNeedSelector /\ g.extraSelectorDerived)
  )

def diagonalHamiltonianOrderingFrontier
    (g : Sym4DiagonalHamiltonianOrderingAuditGate) : Prop :=
  g.HilbertDimensionEquals1001 /\
  g.M31PhysicalBlocksAreEllGPEQ /\
  g.isotropicBlockProfilesEqual70 /\
  Not g.isotropicBlockWeightsOrderAll1001States /\
  g.componentwiseWeightsBreakIsotropyOrNeedSelector /\
  g.genericWeightsRustineWithoutJanusOrigin /\
  Not g.extraSelectorDerived

theorem isotropic_block_degeneracy_blocks_diagonal_hamiltonian_closure
    (g : Sym4DiagonalHamiltonianOrderingAuditGate)
    (hFrontier : diagonalHamiltonianOrderingFrontier g) :
    Not (diagonalHamiltonianOrderingClosed g) := by
  intro h
  rcases h.2.2 with hIso | hSelector
  · exact hFrontier.2.2.2.1 hIso
  · exact hFrontier.2.2.2.2.2.2 hSelector.2

end P0EFTJanusSym4DiagonalHamiltonianOrderingAuditGate
end JanusFormal

import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSym4FiniteTransferOperatorCandidateGate

namespace JanusFormal
namespace P0EFTJanusSym4TransferGeneratorCandidateMatrixGate

set_option autoImplicit false

structure Sym4TransferGeneratorCandidateMatrixGate where
  HilbertSectorIsSym4C11 : Prop
  HilbertDimensionEquals1001 : Prop
  anchoredCasimirOrdersNormalStates : Prop
  anchoredR4NumberOrdersNormalStates : Prop
  anchoredPTModularFlowDerived : Prop
  basisPathGraphOrdersStates : Prop
  basisPathGraphAnchoredInJanusPT : Prop
  boundaryHamiltonianDerivedFromAction : Prop
  boundaryHamiltonianOrdersNormalStates : Prop

def transferGeneratorClosed
    (g : Sym4TransferGeneratorCandidateMatrixGate) : Prop :=
  g.HilbertSectorIsSym4C11 /\
  g.HilbertDimensionEquals1001 /\
  (
    g.anchoredCasimirOrdersNormalStates \/
    g.anchoredR4NumberOrdersNormalStates \/
    (g.anchoredPTModularFlowDerived /\ g.boundaryHamiltonianOrdersNormalStates) \/
    (g.basisPathGraphOrdersStates /\ g.basisPathGraphAnchoredInJanusPT) \/
    (g.boundaryHamiltonianDerivedFromAction /\ g.boundaryHamiltonianOrdersNormalStates)
  )

def transferGeneratorFrontier
    (g : Sym4TransferGeneratorCandidateMatrixGate) : Prop :=
  g.HilbertSectorIsSym4C11 /\
  g.HilbertDimensionEquals1001 /\
  Not g.anchoredCasimirOrdersNormalStates /\
  Not g.anchoredR4NumberOrdersNormalStates /\
  Not g.anchoredPTModularFlowDerived /\
  g.basisPathGraphOrdersStates /\
  Not g.basisPathGraphAnchoredInJanusPT /\
  Not g.boundaryHamiltonianDerivedFromAction

theorem no_anchored_transfer_generator_blocks_closure
    (g : Sym4TransferGeneratorCandidateMatrixGate)
    (hFrontier : transferGeneratorFrontier g) :
    Not (transferGeneratorClosed g) := by
  intro h
  rcases h.2.2 with hCasimir | hR4 | hPT | hPath | hHamiltonian
  · exact hFrontier.2.2.1 hCasimir
  · exact hFrontier.2.2.2.1 hR4
  · exact hFrontier.2.2.2.2.1 hPT.1
  · exact hFrontier.2.2.2.2.2.2.1 hPath.2
  · exact hFrontier.2.2.2.2.2.2.2 hHamiltonian.1

end P0EFTJanusSym4TransferGeneratorCandidateMatrixGate
end JanusFormal

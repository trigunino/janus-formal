import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusM31ToSym4BoundaryRepresentationGapGate

namespace JanusFormal
namespace P0EFTJanusM31CoadjointRhoTransferAttemptGate

set_option autoImplicit false

structure M31CoadjointRhoTransferAttemptGate where
  coadjointRhoCandidateAvailable : Prop
  rhoLiftToSym4Available : Prop
  rotationBlockIsNormalHamiltonian : Prop
  boostBlockIsNormalHamiltonian : Prop
  translationShearIsNormalHamiltonian : Prop
  chargeSectorIsNormalHamiltonian : Prop
  boundaryActionHamiltonianDerived : Prop
  orderedSpectrumMapsToAmin : Prop

def coadjointRhoTransferClosed
    (g : M31CoadjointRhoTransferAttemptGate) : Prop :=
  g.coadjointRhoCandidateAvailable /\
  g.rhoLiftToSym4Available /\
  (
    g.rotationBlockIsNormalHamiltonian \/
    g.boostBlockIsNormalHamiltonian \/
    g.translationShearIsNormalHamiltonian \/
    g.chargeSectorIsNormalHamiltonian \/
    g.boundaryActionHamiltonianDerived
  ) /\
  g.orderedSpectrumMapsToAmin

def coadjointRhoTransferFrontier
    (g : M31CoadjointRhoTransferAttemptGate) : Prop :=
  g.coadjointRhoCandidateAvailable /\
  g.rhoLiftToSym4Available /\
  Not g.rotationBlockIsNormalHamiltonian /\
  Not g.boostBlockIsNormalHamiltonian /\
  Not g.translationShearIsNormalHamiltonian /\
  Not g.chargeSectorIsNormalHamiltonian /\
  Not g.boundaryActionHamiltonianDerived

theorem coadjoint_rho_without_normal_hamiltonian_blocks_transfer_closure
    (g : M31CoadjointRhoTransferAttemptGate)
    (hFrontier : coadjointRhoTransferFrontier g) :
    Not (coadjointRhoTransferClosed g) := by
  intro h
  rcases h.2.2.1 with hRot | hBoost | hTrans | hCharge | hBoundary
  · exact hFrontier.2.2.1 hRot
  · exact hFrontier.2.2.2.1 hBoost
  · exact hFrontier.2.2.2.2.1 hTrans
  · exact hFrontier.2.2.2.2.2.1 hCharge
  · exact hFrontier.2.2.2.2.2.2 hBoundary

end P0EFTJanusM31CoadjointRhoTransferAttemptGate
end JanusFormal

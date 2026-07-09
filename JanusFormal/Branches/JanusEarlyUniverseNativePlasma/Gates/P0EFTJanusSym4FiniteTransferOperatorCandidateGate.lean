import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSym4NormalChannelSpectralOperatorCandidateGate

namespace JanusFormal
namespace P0EFTJanusSym4FiniteTransferOperatorCandidateGate

set_option autoImplicit false

structure Sym4FiniteTransferOperatorCandidateGate where
  HilbertSectorIsSym4C11 : Prop
  HilbertDimensionEquals1001 : Prop
  finiteNIntrinsicToHilbertSector : Prop
  finiteTransferMatrixOnSym4Defined : Prop
  transferRuleUnitaryOrSelfAdjoint : Prop
  Z2PTSymmetryCommutesWithTransfer : Prop
  orderedNormalResolutionSpectrumDerived : Prop
  aminEqualsInverseEndpointCountProved : Prop
  photonBaryonDragUsesSameTransferClock : Prop

def finiteTransferOperatorClosed
    (g : Sym4FiniteTransferOperatorCandidateGate) : Prop :=
  g.HilbertSectorIsSym4C11 /\
  g.HilbertDimensionEquals1001 /\
  g.finiteNIntrinsicToHilbertSector /\
  g.finiteTransferMatrixOnSym4Defined /\
  g.transferRuleUnitaryOrSelfAdjoint /\
  g.Z2PTSymmetryCommutesWithTransfer /\
  g.orderedNormalResolutionSpectrumDerived /\
  g.aminEqualsInverseEndpointCountProved /\
  g.photonBaryonDragUsesSameTransferClock

def finiteTransferOperatorFrontier
    (g : Sym4FiniteTransferOperatorCandidateGate) : Prop :=
  g.HilbertSectorIsSym4C11 /\
  g.HilbertDimensionEquals1001 /\
  g.finiteNIntrinsicToHilbertSector /\
  Not g.finiteTransferMatrixOnSym4Defined /\
  Not g.orderedNormalResolutionSpectrumDerived

theorem missing_transfer_matrix_blocks_finite_transfer_closure
    (g : Sym4FiniteTransferOperatorCandidateGate)
    (hFrontier : finiteTransferOperatorFrontier g) :
    Not (finiteTransferOperatorClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusSym4FiniteTransferOperatorCandidateGate
end JanusFormal

import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSym4LinearResolutionLawCandidateGate

namespace JanusFormal
namespace P0EFTJanusSym4NormalChannelSpectralOperatorCandidateGate

set_option autoImplicit false

structure Sym4NormalChannelSpectralOperatorCandidateGate where
  NFromSym4C11Equals1001 : Prop
  selfAdjointOneDimensionalNormalOperatorDeclared : Prop
  linearModeIndexingAvailable : Prop
  spectrumInfiniteWithoutCutoff : Prop
  finiteNSelectedByOperatorAlone : Prop
  finiteNSelectedBySym4BoundarySector : Prop
  boundaryStateLawDerivesFiniteBandlimit : Prop
  aminEqualsInverseBandlimitProved : Prop
  photonRulerUsesSameNormalChannel : Prop

def normalChannelSpectralOperatorClosed
    (g : Sym4NormalChannelSpectralOperatorCandidateGate) : Prop :=
  g.NFromSym4C11Equals1001 /\
  g.selfAdjointOneDimensionalNormalOperatorDeclared /\
  g.linearModeIndexingAvailable /\
  g.finiteNSelectedBySym4BoundarySector /\
  g.boundaryStateLawDerivesFiniteBandlimit /\
  g.aminEqualsInverseBandlimitProved /\
  g.photonRulerUsesSameNormalChannel

def normalChannelSpectralOperatorFrontier
    (g : Sym4NormalChannelSpectralOperatorCandidateGate) : Prop :=
  g.NFromSym4C11Equals1001 /\
  g.selfAdjointOneDimensionalNormalOperatorDeclared /\
  g.linearModeIndexingAvailable /\
  g.spectrumInfiniteWithoutCutoff /\
  Not g.finiteNSelectedByOperatorAlone /\
  g.finiteNSelectedBySym4BoundarySector /\
  Not g.boundaryStateLawDerivesFiniteBandlimit

theorem infinite_spectrum_without_boundary_law_blocks_operator_closure
    (g : Sym4NormalChannelSpectralOperatorCandidateGate)
    (hFrontier : normalChannelSpectralOperatorFrontier g) :
    Not (normalChannelSpectralOperatorClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2.2 h.2.2.2.2.1

end P0EFTJanusSym4NormalChannelSpectralOperatorCandidateGate
end JanusFormal

import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusBoundaryDimensionToAminMapAuditGate

namespace JanusFormal
namespace P0EFTJanusSym4LinearResolutionLawCandidateGate

set_option autoImplicit false

structure Sym4LinearResolutionLawCandidateGate where
  NFromSym4C11Equals1001 : Prop
  earlyBranchHasOneDimensionalNormalChannel : Prop
  normalChannelSpectralOperatorDefined : Prop
  sym4StatesIdentifyNormalResolutionCells : Prop
  aminEqualsInverseStateCountProved : Prop
  photonRulerMapProved : Prop

def sym4LinearResolutionLawClosed
    (g : Sym4LinearResolutionLawCandidateGate) : Prop :=
  g.NFromSym4C11Equals1001 /\
  g.earlyBranchHasOneDimensionalNormalChannel /\
  g.normalChannelSpectralOperatorDefined /\
  g.sym4StatesIdentifyNormalResolutionCells /\
  g.aminEqualsInverseStateCountProved /\
  g.photonRulerMapProved

theorem no_normal_operator_blocks_linear_resolution_law
    (g : Sym4LinearResolutionLawCandidateGate)
    (hNoOperator : Not g.normalChannelSpectralOperatorDefined) :
    Not (sym4LinearResolutionLawClosed g) := by
  intro h
  exact hNoOperator h.2.2.1

end P0EFTJanusSym4LinearResolutionLawCandidateGate
end JanusFormal

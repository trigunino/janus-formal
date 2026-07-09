import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusBoundaryStateLawCandidateMatrixGate

namespace JanusFormal
namespace P0EFTJanusM31TorsorCPTExteriorPowerCandidateGate

set_option autoImplicit false

structure M31TorsorCPTExteriorPowerCandidateGate where
  M31JanusLieDimension11 : Prop
  M31CPTIndependentGenerators3 : Prop
  primitiveCount14Computed : Prop
  exteriorDegree4Declared : Prop
  choose14_4Equals1001 : Prop
  matchesRequiredN : Prop
  continuousTorsorAndDiscreteCPTMixingDeclared : Prop
  boundaryExteriorHilbertLawDerived : Prop
  fourExcitationSectorSelected : Prop
  mapsToAminAndPhotonRuler : Prop

def m31ExteriorPowerCandidateReady
    (g : M31TorsorCPTExteriorPowerCandidateGate) : Prop :=
  g.M31JanusLieDimension11 /\
  g.M31CPTIndependentGenerators3 /\
  g.primitiveCount14Computed /\
  g.exteriorDegree4Declared /\
  g.choose14_4Equals1001 /\
  g.matchesRequiredN /\
  g.continuousTorsorAndDiscreteCPTMixingDeclared

def m31ExteriorPowerStateLawDerived
    (g : M31TorsorCPTExteriorPowerCandidateGate) : Prop :=
  m31ExteriorPowerCandidateReady g /\
  g.boundaryExteriorHilbertLawDerived /\
  g.fourExcitationSectorSelected /\
  g.mapsToAminAndPhotonRuler

theorem candidate_without_boundary_hilbert_law_not_state_law
    (g : M31TorsorCPTExteriorPowerCandidateGate)
    (_hCandidate : m31ExteriorPowerCandidateReady g)
    (hNoHilbert : Not g.boundaryExteriorHilbertLawDerived) :
    Not (m31ExteriorPowerStateLawDerived g) := by
  intro h
  exact hNoHilbert h.right.left

end P0EFTJanusM31TorsorCPTExteriorPowerCandidateGate
end JanusFormal

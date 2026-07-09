namespace JanusFormal
namespace P0EFTJanusPhaseSpaceOccupationSearchGate

set_option autoImplicit false

structure PhaseSpaceOccupationSearchGate where
  requiredExponentIsThree : Prop
  constantTopologyRejected : Prop
  sigmaAreaInsufficient : Prop
  quantumCellH3Rejected : Prop
  sigmaVolumeCandidate : Prop
  horizonVolumeCandidate : Prop
  adiabaticRadiationFirstLawCandidate : Prop
  negativeSectorEntropyProjectionOpen : Prop
  noCandidatePromotedAsProven : Prop

def searchAtCurrentFrontier (g : PhaseSpaceOccupationSearchGate) : Prop :=
  g.requiredExponentIsThree /\
  g.constantTopologyRejected /\
  g.sigmaAreaInsufficient /\
  g.quantumCellH3Rejected /\
  g.sigmaVolumeCandidate /\
  g.horizonVolumeCandidate /\
  g.adiabaticRadiationFirstLawCandidate /\
  g.negativeSectorEntropyProjectionOpen /\
  g.noCandidatePromotedAsProven

theorem occupation_search_keeps_candidates_conditional
    (g : PhaseSpaceOccupationSearchGate)
    (h : searchAtCurrentFrontier g) :
    g.noCandidatePromotedAsProven := by
  exact h.2.2.2.2.2.2.2.2

end P0EFTJanusPhaseSpaceOccupationSearchGate
end JanusFormal

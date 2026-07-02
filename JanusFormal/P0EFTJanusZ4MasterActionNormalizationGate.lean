import JanusFormal.P0EFTJanusZ4MasterRegularizedDiagnosticShapeReportGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterActionNormalizationGate

set_option autoImplicit false

structure MasterActionNormalizationGate where
  regularizedShapeReportGatePassed : Prop
  regularizedShapeLockCleared : Prop
  membraneTransportShapeAvailable : Prop
  fullUpstreamActionNormalizationDerived : Prop
  normalizationFromZ4ActionFunctional : Prop
  normalizationFromMembraneJunctionTerms : Prop
  normalizationFromOrbifoldBoundaryConditions : Prop
  actionNormalizationGatePassed : Prop
  likelihoodHandshakeAllowed : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def normalizationBlocked (g : MasterActionNormalizationGate) : Prop :=
  g.regularizedShapeReportGatePassed /\
  g.regularizedShapeLockCleared /\
  g.membraneTransportShapeAvailable /\
  Not g.fullUpstreamActionNormalizationDerived /\
  Not g.normalizationFromZ4ActionFunctional /\
  Not g.normalizationFromMembraneJunctionTerms /\
  Not g.normalizationFromOrbifoldBoundaryConditions /\
  Not g.actionNormalizationGatePassed /\
  Not g.likelihoodHandshakeAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

def normalizationReady (g : MasterActionNormalizationGate) : Prop :=
  g.regularizedShapeReportGatePassed /\
  g.regularizedShapeLockCleared /\
  g.membraneTransportShapeAvailable /\
  g.fullUpstreamActionNormalizationDerived /\
  g.normalizationFromZ4ActionFunctional /\
  g.normalizationFromMembraneJunctionTerms /\
  g.normalizationFromOrbifoldBoundaryConditions /\
  g.actionNormalizationGatePassed /\
  g.likelihoodHandshakeAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem missing_action_normalization_blocks_likelihood
    (g : MasterActionNormalizationGate)
    (h : normalizationBlocked g) :
    Not g.likelihoodHandshakeAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hLikelihood, _, _, _, _⟩
  exact hLikelihood

theorem action_normalization_allows_handshake_not_planck
    (g : MasterActionNormalizationGate)
    (h : normalizationReady g) :
    g.likelihoodHandshakeAllowed /\ Not g.officialPlanckTrialAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hHandshake, hPlanck, _, _, _⟩
  exact ⟨hHandshake, hPlanck⟩

end P0EFTJanusZ4MasterActionNormalizationGate
end JanusFormal

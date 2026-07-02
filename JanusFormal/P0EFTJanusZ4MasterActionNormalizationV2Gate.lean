import JanusFormal.P0EFTJanusZ4MasterPreLikelihoodLockV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterActionNormalizationV2Gate

set_option autoImplicit false

structure MasterActionNormalizationV2Gate where
  preLikelihoodLockV2Cleared : Prop
  selectedRevisionDeclared : Prop
  sharedUZ4NormalizationPresent : Prop
  silkGuardDeclaredUpstream : Prop
  normalizationFromSelectedMasterRevision : Prop
  normalizationFromSharedUZ4Scale : Prop
  normalizationFromZ4ActionFunctional : Prop
  normalizationFromMembraneJunctionTerms : Prop
  normalizationFromOrbifoldBoundaryConditions : Prop
  fullUpstreamActionNormalizationDerived : Prop
  actionNormalizationV2GatePassed : Prop
  likelihoodHandshakeAllowed : Prop
  officialPlanckTrialAllowed : Prop
  likelihoodEvaluationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def normalizationV2Ready (g : MasterActionNormalizationV2Gate) : Prop :=
  g.preLikelihoodLockV2Cleared /\
  g.selectedRevisionDeclared /\
  g.sharedUZ4NormalizationPresent /\
  g.silkGuardDeclaredUpstream /\
  g.normalizationFromSelectedMasterRevision /\
  g.normalizationFromSharedUZ4Scale /\
  g.normalizationFromZ4ActionFunctional /\
  g.normalizationFromMembraneJunctionTerms /\
  g.normalizationFromOrbifoldBoundaryConditions /\
  g.fullUpstreamActionNormalizationDerived /\
  g.actionNormalizationV2GatePassed /\
  g.likelihoodHandshakeAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem action_normalization_v2_allows_handshake_only
    (g : MasterActionNormalizationV2Gate)
    (h : normalizationV2Ready g) :
    g.likelihoodHandshakeAllowed /\ Not g.officialPlanckTrialAllowed /\ Not g.likelihoodEvaluationAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hHandshake, hNoPlanck, hNoLikelihood, _, _, _⟩
  exact ⟨hHandshake, hNoPlanck, hNoLikelihood⟩

end P0EFTJanusZ4MasterActionNormalizationV2Gate
end JanusFormal

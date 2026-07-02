import JanusFormal.P0EFTJanusZ4MasterDiagnosticShapeReportV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterPreLikelihoodLockV2Gate

set_option autoImplicit false

structure MasterPreLikelihoodLockV2Gate where
  shapeReportV2GatePassed : Prop
  phaseGuardPassed : Prop
  amplitudeGuardPassed : Prop
  zeroArtifactGuardPassed : Prop
  nonoverlapAccountingBasisDeclared : Prop
  overlappingSumForbidden : Prop
  reportedTotalUsesOneHighLBasisOnly : Prop
  preLikelihoodLockActive : Prop
  preLikelihoodLockCleared : Prop
  diagnosticSpectraRemainAvailable : Prop
  likelihoodHandshakeAllowed : Prop
  officialPlanckTrialAllowed : Prop
  likelihoodEvaluationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def clearedReady (g : MasterPreLikelihoodLockV2Gate) : Prop :=
  g.shapeReportV2GatePassed /\
  g.phaseGuardPassed /\
  g.amplitudeGuardPassed /\
  g.zeroArtifactGuardPassed /\
  g.nonoverlapAccountingBasisDeclared /\
  g.overlappingSumForbidden /\
  g.reportedTotalUsesOneHighLBasisOnly /\
  Not g.preLikelihoodLockActive /\
  g.preLikelihoodLockCleared /\
  g.diagnosticSpectraRemainAvailable /\
  g.likelihoodHandshakeAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

def blockedReady (g : MasterPreLikelihoodLockV2Gate) : Prop :=
  g.shapeReportV2GatePassed /\
  g.preLikelihoodLockActive /\
  Not g.preLikelihoodLockCleared /\
  g.diagnosticSpectraRemainAvailable /\
  Not g.likelihoodHandshakeAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem pre_likelihood_lock_v2_never_promotes
    (g : MasterPreLikelihoodLockV2Gate)
    (h : clearedReady g \/ blockedReady g) :
    Not g.officialPlanckTrialAllowed /\ Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  cases h with
  | inl hCleared =>
      rcases hCleared with ⟨_, _, _, _, _, _, _, _, _, _, _, hNoPlanck, _, hNoPromotion, _, hNoFull⟩
      exact ⟨hNoPlanck, hNoPromotion, hNoFull⟩
  | inr hBlocked =>
      rcases hBlocked with ⟨_, _, _, _, _, hNoPlanck, _, hNoPromotion, _, hNoFull⟩
      exact ⟨hNoPlanck, hNoPromotion, hNoFull⟩

theorem cleared_v2_allows_handshake_only
    (g : MasterPreLikelihoodLockV2Gate)
    (h : clearedReady g) :
    g.likelihoodHandshakeAllowed /\ Not g.likelihoodEvaluationAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hHandshake, _, hNoLikelihood, _, _, _⟩
  exact ⟨hHandshake, hNoLikelihood⟩

end P0EFTJanusZ4MasterPreLikelihoodLockV2Gate
end JanusFormal

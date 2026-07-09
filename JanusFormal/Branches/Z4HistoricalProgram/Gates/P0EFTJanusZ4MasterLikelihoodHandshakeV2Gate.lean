import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MasterActionNormalizationV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterLikelihoodHandshakeV2Gate

set_option autoImplicit false

structure MasterLikelihoodHandshakeV2Gate where
  actionNormalizationV2GatePassed : Prop
  diagnosticSpectraV2Generated : Prop
  shapeV2GuardsPassed : Prop
  nonoverlapAccountingBasisDeclared : Prop
  carrierThresholdPassed : Prop
  spectraPathsExist : Prop
  likelihoodHandshakeV2Passed : Prop
  diagnosticLikelihoodInputReady : Prop
  likelihoodEvaluationAllowed : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def handshakeV2Ready (g : MasterLikelihoodHandshakeV2Gate) : Prop :=
  g.actionNormalizationV2GatePassed /\
  g.diagnosticSpectraV2Generated /\
  g.shapeV2GuardsPassed /\
  g.nonoverlapAccountingBasisDeclared /\
  g.carrierThresholdPassed /\
  g.spectraPathsExist /\
  g.likelihoodHandshakeV2Passed /\
  g.diagnosticLikelihoodInputReady /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem handshake_v2_allows_diagnostic_input_only
    (g : MasterLikelihoodHandshakeV2Gate)
    (h : handshakeV2Ready g) :
    g.diagnosticLikelihoodInputReady /\
      Not g.likelihoodEvaluationAllowed /\
      Not g.officialPlanckTrialAllowed := by
  rcases h with ⟨_, _, _, _, _, _, _, hInput, hNoLikelihood, hNoPlanck, _, _, _⟩
  exact ⟨hInput, hNoLikelihood, hNoPlanck⟩

end P0EFTJanusZ4MasterLikelihoodHandshakeV2Gate
end JanusFormal

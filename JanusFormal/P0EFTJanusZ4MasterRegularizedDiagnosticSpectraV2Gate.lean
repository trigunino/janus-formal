import JanusFormal.P0EFTJanusZ4MasterRevisedCarrierTangentProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterRegularizedDiagnosticSpectraV2Gate

set_option autoImplicit false

structure MasterRegularizedDiagnosticSpectraV2Gate where
  revisedCarrierTangentProjectionPassed : Prop
  diagnosticSpectraV2Generated : Prop
  sourceLevelPayloadReplayedAfterSerialization : Prop
  carrierThresholdPassedAfterSerialization : Prop
  officialPlanckTrialAllowed : Prop
  likelihoodEvaluationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def diagnosticSpectraV2Ready (g : MasterRegularizedDiagnosticSpectraV2Gate) : Prop :=
  g.revisedCarrierTangentProjectionPassed /\
  g.diagnosticSpectraV2Generated /\
  g.sourceLevelPayloadReplayedAfterSerialization /\
  g.carrierThresholdPassedAfterSerialization /\
  Not g.officialPlanckTrialAllowed /\
  Not g.likelihoodEvaluationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem diagnostic_spectra_v2_remain_pre_likelihood
    (g : MasterRegularizedDiagnosticSpectraV2Gate)
    (hPolicy : diagnosticSpectraV2Ready g -> g.gatePassed)
    (h : diagnosticSpectraV2Ready g) :
    g.gatePassed /\ Not g.likelihoodEvaluationAllowed /\ Not g.candidatePromotionAllowed := by
  have hGate : g.gatePassed := hPolicy h
  rcases h with ⟨_, _, _, _, _, hNoLikelihood, hNoPromotion, _, _⟩
  exact ⟨hGate, hNoLikelihood, hNoPromotion⟩

end P0EFTJanusZ4MasterRegularizedDiagnosticSpectraV2Gate
end JanusFormal

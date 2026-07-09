import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MasterActionNormalizationGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterLikelihoodHandshakeGate

set_option autoImplicit false

structure MasterLikelihoodHandshakeGate where
  actionNormalizationGatePassed : Prop
  regularizedDiagnosticSpectraGenerated : Prop
  regularizedShapeLockCleared : Prop
  carrierThresholdPassed : Prop
  spectraPathsExist : Prop
  likelihoodHandshakePassed : Prop
  diagnosticLikelihoodInputReady : Prop
  officialPlanckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def handshakeReady (g : MasterLikelihoodHandshakeGate) : Prop :=
  g.actionNormalizationGatePassed /\
  g.regularizedDiagnosticSpectraGenerated /\
  g.regularizedShapeLockCleared /\
  g.carrierThresholdPassed /\
  g.spectraPathsExist /\
  g.likelihoodHandshakePassed /\
  g.diagnosticLikelihoodInputReady /\
  Not g.officialPlanckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem handshake_allows_diagnostic_input_not_planck
    (g : MasterLikelihoodHandshakeGate)
    (h : handshakeReady g) :
    g.diagnosticLikelihoodInputReady /\ Not g.officialPlanckTrialAllowed := by
  rcases h with ⟨_, _, _, _, _, _, hInput, hPlanck, _, _, _⟩
  exact ⟨hInput, hPlanck⟩

end P0EFTJanusZ4MasterLikelihoodHandshakeGate
end JanusFormal

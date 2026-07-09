import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterAcousticCalculatorShapePhaseDampingGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterSolverProvenanceManifestGate

set_option autoImplicit false

structure MasterSolverProvenanceManifestGate where
  shapeDiagnosticsReady : Prop
  manifestWritten : Prop
  componentSpectraHashesRecorded : Prop
  calculatorPayloadHashRecorded : Prop
  unlensedLensedProvenanceDeclared : Prop
  observedLikelihoodAllowed : Prop
  planckRetryAllowed : Prop
  candidatePromotionAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def provenanceReady (g : MasterSolverProvenanceManifestGate) : Prop :=
  g.shapeDiagnosticsReady /\
  g.manifestWritten /\
  g.componentSpectraHashesRecorded /\
  g.calculatorPayloadHashRecorded /\
  g.unlensedLensedProvenanceDeclared /\
  Not g.observedLikelihoodAllowed /\
  Not g.planckRetryAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem provenance_blocks_observed_claims
    (g : MasterSolverProvenanceManifestGate)
    (h : provenanceReady g) :
    Not g.observedLikelihoodAllowed /\ Not g.fullPlanckValidation := by
  rcases h with ⟨_, _, _, _, _, hLike, _, _, _, hFull⟩
  exact ⟨hLike, hFull⟩

end P0EFTJanusZ4MasterSolverProvenanceManifestGate
end JanusFormal

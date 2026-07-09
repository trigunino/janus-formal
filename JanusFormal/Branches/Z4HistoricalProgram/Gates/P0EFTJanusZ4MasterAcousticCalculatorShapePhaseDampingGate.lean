import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MasterAcousticCalculatorComponentSpectraGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterAcousticCalculatorShapePhaseDampingGate

set_option autoImplicit false

structure MasterAcousticCalculatorShapePhaseDampingGate where
  componentSpectraReady : Prop
  shapePhaseDampingDiagnosticsReady : Prop
  observedLikelihoodAllowed : Prop
  planckRetryAllowed : Prop
  candidatePromotionAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def diagnosticsReady (g : MasterAcousticCalculatorShapePhaseDampingGate) : Prop :=
  g.componentSpectraReady /\
  g.shapePhaseDampingDiagnosticsReady /\
  Not g.observedLikelihoodAllowed /\
  Not g.planckRetryAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem diagnostics_do_not_validate_planck
    (g : MasterAcousticCalculatorShapePhaseDampingGate)
    (h : diagnosticsReady g) :
    Not g.planckRetryAllowed /\ Not g.fullPlanckValidation := by
  rcases h with ⟨_, _, _, hRetry, _, _, hFull⟩
  exact ⟨hRetry, hFull⟩

end P0EFTJanusZ4MasterAcousticCalculatorShapePhaseDampingGate
end JanusFormal

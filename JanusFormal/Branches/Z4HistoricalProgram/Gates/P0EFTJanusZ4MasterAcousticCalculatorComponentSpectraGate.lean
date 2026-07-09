import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MasterPhotonBaryonAcousticCalculatorGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterAcousticCalculatorComponentSpectraGate

set_option autoImplicit false

structure MasterAcousticCalculatorComponentSpectraGate where
  calculatorDiagnosticReady : Prop
  componentSpectraGenerated : Prop
  sourceComponentsWritten : Prop
  unlensedLensedSplitAvailable : Prop
  observedLikelihoodAllowed : Prop
  planckRetryAllowed : Prop
  candidatePromotionAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def componentSpectraReady (g : MasterAcousticCalculatorComponentSpectraGate) : Prop :=
  g.calculatorDiagnosticReady /\
  g.componentSpectraGenerated /\
  g.sourceComponentsWritten /\
  Not g.observedLikelihoodAllowed /\
  Not g.planckRetryAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem component_spectra_are_internal_only
    (g : MasterAcousticCalculatorComponentSpectraGate)
    (h : componentSpectraReady g) :
    Not g.observedLikelihoodAllowed /\ Not g.fullPlanckValidation := by
  rcases h with ⟨_, _, _, hLike, _, _, _, hFull⟩
  exact ⟨hLike, hFull⟩

end P0EFTJanusZ4MasterAcousticCalculatorComponentSpectraGate
end JanusFormal

import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MasterSolverImplementationReadinessGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterUnlensedLensedSplitGate

set_option autoImplicit false

structure MasterUnlensedLensedSplitGate where
  unlensedSourceSpectraGenerated : Prop
  lensedRemapGenerated : Prop
  unlensedLensedSplitAvailable : Prop
  physicalLensingSolver : Prop
  observedLikelihoodAllowed : Prop
  planckRetryAllowed : Prop
  candidatePromotionAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def splitReady (g : MasterUnlensedLensedSplitGate) : Prop :=
  g.unlensedSourceSpectraGenerated /\
  g.lensedRemapGenerated /\
  g.unlensedLensedSplitAvailable /\
  Not g.observedLikelihoodAllowed /\
  Not g.planckRetryAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem split_is_not_validation
    (g : MasterUnlensedLensedSplitGate)
    (h : splitReady g) :
    Not g.planckRetryAllowed /\ Not g.fullPlanckValidation := by
  rcases h with ⟨_, _, _, _, hRetry, _, _, hFull⟩
  exact ⟨hRetry, hFull⟩

end P0EFTJanusZ4MasterUnlensedLensedSplitGate
end JanusFormal

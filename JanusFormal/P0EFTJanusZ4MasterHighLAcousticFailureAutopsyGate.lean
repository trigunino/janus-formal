import JanusFormal.P0EFTJanusZ4MasterObservedFailureMapV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterHighLAcousticFailureAutopsyGate

set_option autoImplicit false

structure MasterHighLAcousticFailureAutopsyGate where
  observedFailureMapV2Rejected : Prop
  highLAcousticShapeFailure : Prop
  peakDiagnosticsDeclared : Prop
  teZeroDiagnosticsDeclared : Prop
  dampingTailDiagnosticsDeclared : Prop
  unlensedLensedSplitAvailable : Prop
  sourceComponentAttributionComplete : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  newPhysicsAllowed : Prop
  retuningAllowed : Prop
  planckRetryAllowed : Prop
  fullPlanckValidation : Prop

def autopsyReady (g : MasterHighLAcousticFailureAutopsyGate) : Prop :=
  g.observedFailureMapV2Rejected /\
  g.highLAcousticShapeFailure /\
  g.peakDiagnosticsDeclared /\
  g.teZeroDiagnosticsDeclared /\
  g.dampingTailDiagnosticsDeclared /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.newPhysicsAllowed /\
  Not g.retuningAllowed /\
  Not g.planckRetryAllowed /\
  Not g.fullPlanckValidation

theorem autopsy_blocks_repair_attempts
    (g : MasterHighLAcousticFailureAutopsyGate)
    (h : autopsyReady g) :
    Not g.candidatePromotionAllowed /\ Not g.newPhysicsAllowed /\
    Not g.retuningAllowed /\ Not g.planckRetryAllowed /\ Not g.fullPlanckValidation := by
  rcases h with
    ⟨_, _, _, _, _, hPromotion, _, hPhysics, hRetuning, hRetry, hFull⟩
  exact ⟨hPromotion, hPhysics, hRetuning, hRetry, hFull⟩

theorem missing_unlensed_or_source_split_prevents_closure
    (g : MasterHighLAcousticFailureAutopsyGate)
    (hReady : autopsyReady g)
    (_ : Not g.unlensedLensedSplitAvailable \/ Not g.sourceComponentAttributionComplete) :
    Not g.fullPlanckValidation := by
  exact (autopsy_blocks_repair_attempts g hReady).right.right.right.right

end P0EFTJanusZ4MasterHighLAcousticFailureAutopsyGate
end JanusFormal

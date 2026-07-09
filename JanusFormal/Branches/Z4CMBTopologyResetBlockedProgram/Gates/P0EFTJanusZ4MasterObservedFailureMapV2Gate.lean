import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterObservedNonOverlapAccountingV2Gate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedFailureMapV2Gate

set_option autoImplicit false

structure MasterObservedFailureMapV2Gate where
  observedTrialExecuted : Prop
  observedMasterV2BranchRejected : Prop
  highlFailureDominates : Prop
  lowLFailureDominates : Prop
  lensingRescueInsufficient : Prop
  highLAcousticShapeFailure : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop
  newPhysicsAllowed : Prop
  retuningAllowed : Prop

def highLFailureV2Ready (g : MasterObservedFailureMapV2Gate) : Prop :=
  g.observedTrialExecuted /\
  g.observedMasterV2BranchRejected /\
  g.highlFailureDominates /\
  Not g.lowLFailureDominates /\
  g.lensingRescueInsufficient /\
  g.highLAcousticShapeFailure /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation /\
  Not g.newPhysicsAllowed /\
  Not g.retuningAllowed

theorem high_l_failure_v2_blocks_promotion_and_retuning
    (g : MasterObservedFailureMapV2Gate)
    (h : highLFailureV2Ready g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation /\
    Not g.newPhysicsAllowed /\ Not g.retuningAllowed := by
  rcases h with
    âŸ¨_, _, _, _, _, _, hPromotion, _, hFull, hPhysics, hRetuningâŸ©
  exact âŸ¨hPromotion, hFull, hPhysics, hRetuningâŸ©

end P0EFTJanusZ4MasterObservedFailureMapV2Gate
end JanusFormal

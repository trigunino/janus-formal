import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterObservedNonOverlapAccountingGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterObservedFailureMapGate

set_option autoImplicit false

structure MasterObservedFailureMapGate where
  observedMasterBranchRejected : Prop
  highlFailureDominates : Prop
  lowLFailureDominates : Prop
  lensingRescueInsufficient : Prop
  highLAcousticShapeFailure : Prop
  candidatePromotionAllowed : Prop
  observationalClaimAllowed : Prop
  fullPlanckValidation : Prop

def highLFailureReady (g : MasterObservedFailureMapGate) : Prop :=
  g.observedMasterBranchRejected /\
  g.highlFailureDominates /\
  Not g.lowLFailureDominates /\
  g.lensingRescueInsufficient /\
  g.highLAcousticShapeFailure /\
  Not g.candidatePromotionAllowed /\
  Not g.observationalClaimAllowed /\
  Not g.fullPlanckValidation

theorem high_l_failure_blocks_promotion
    (g : MasterObservedFailureMapGate)
    (h : highLFailureReady g) :
    Not g.candidatePromotionAllowed /\ Not g.fullPlanckValidation := by
  rcases h with âŸ¨_, _, _, _, _, hPromotion, _, hFullâŸ©
  exact âŸ¨hPromotion, hFullâŸ©

end P0EFTJanusZ4MasterObservedFailureMapGate
end JanusFormal

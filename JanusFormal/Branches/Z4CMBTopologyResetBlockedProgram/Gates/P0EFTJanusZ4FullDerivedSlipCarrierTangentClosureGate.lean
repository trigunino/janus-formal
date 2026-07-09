import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4DerivedSlipCarrierTangentProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ4FullDerivedSlipCarrierTangentClosureGate

set_option autoImplicit false

structure FullDerivedSlipCarrierTangentClosureGate where
  fullDerivedSlipCarrierTangent : Prop
  closureRecommended : Prop
  dominantTangentDirectionReported : Prop
  candidatePromotionAllowed : Prop
  planckTrialAllowed : Prop
  noLambdaRetuning : Prop
  noFreeSlipParameter : Prop
  noFreeEtaRatio : Prop
  noDirectClPatch : Prop
  rawToyLOSForbidden : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def carrierTangentClosureReady
    (g : FullDerivedSlipCarrierTangentClosureGate) : Prop :=
  g.fullDerivedSlipCarrierTangent /\
  g.closureRecommended /\
  g.dominantTangentDirectionReported /\
  Not g.candidatePromotionAllowed /\
  Not g.planckTrialAllowed /\
  g.noLambdaRetuning /\
  g.noFreeSlipParameter /\
  g.noFreeEtaRatio /\
  g.noDirectClPatch /\
  g.rawToyLOSForbidden /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem full_derived_slip_closure_blocks_promotion
    (g : FullDerivedSlipCarrierTangentClosureGate)
    (hPolicy : carrierTangentClosureReady g -> g.gatePassed)
    (h : carrierTangentClosureReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4FullDerivedSlipCarrierTangentClosureGate
end JanusFormal

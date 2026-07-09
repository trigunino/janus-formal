import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DerivedSlipCarrierTangentProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ4FullDerivedSlipCarrierArchiveGate

set_option autoImplicit false

structure FullDerivedSlipCarrierArchiveGate where
  fullDerivedSlipCarrierTangent : Prop
  archiveFast : Prop
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

def archiveReady (g : FullDerivedSlipCarrierArchiveGate) : Prop :=
  g.fullDerivedSlipCarrierTangent /\
  g.archiveFast /\
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

theorem full_derived_slip_archive_blocks_promotion
    (g : FullDerivedSlipCarrierArchiveGate)
    (hPolicy : archiveReady g -> g.gatePassed)
    (h : archiveReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4FullDerivedSlipCarrierArchiveGate
end JanusFormal

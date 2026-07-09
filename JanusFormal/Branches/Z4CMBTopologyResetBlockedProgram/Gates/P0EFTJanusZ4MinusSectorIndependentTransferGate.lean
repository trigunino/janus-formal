import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ProjectionParityPreservationGate

namespace JanusFormal
namespace P0EFTJanusZ4MinusSectorIndependentTransferGate

set_option autoImplicit false

structure MinusSectorIndependentTransferGate where
  projectionParityGatePassed : Prop
  densityTransferAudited : Prop
  velocityTransferAudited : Prop
  shearTransferAudited : Prop
  weylTransferAudited : Prop
  theta0TransferAudited : Prop
  piTransferAudited : Prop
  projectionSourceTransferAudited : Prop
  bestAmplitudeRescalingReported : Prop
  residualAfterBestAmplitudeFitReported : Prop
  phaseLagReported : Prop
  kDependenceScoreReported : Prop
  tauDependenceScoreReported : Prop
  effectiveTransferRankReported : Prop
  noRhoEffShortcut : Prop
  directClPatchForbidden : Prop
  rawToyLOSForbidden : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  projectionRetuningAllowed : Prop
  freeMinusAmplitudeAllowed : Prop
  hiddenRescalingCoefficientAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def transferAuditReady (g : MinusSectorIndependentTransferGate) : Prop :=
  g.projectionParityGatePassed /\
  g.densityTransferAudited /\
  g.velocityTransferAudited /\
  g.shearTransferAudited /\
  g.weylTransferAudited /\
  g.theta0TransferAudited /\
  g.piTransferAudited /\
  g.projectionSourceTransferAudited /\
  g.bestAmplitudeRescalingReported /\
  g.residualAfterBestAmplitudeFitReported /\
  g.phaseLagReported /\
  g.kDependenceScoreReported /\
  g.tauDependenceScoreReported /\
  g.effectiveTransferRankReported /\
  g.noRhoEffShortcut /\
  g.directClPatchForbidden /\
  g.rawToyLOSForbidden /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.projectionRetuningAllowed /\
  Not g.freeMinusAmplitudeAllowed /\
  Not g.hiddenRescalingCoefficientAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem minus_sector_transfer_audit_blocks_observational_use
    (g : MinusSectorIndependentTransferGate)
    (hPolicy : transferAuditReady g -> g.gatePassed)
    (h : transferAuditReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MinusSectorIndependentTransferGate
end JanusFormal

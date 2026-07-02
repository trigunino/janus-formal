import JanusFormal.P0EFTJanusZ4TwoSectorSourceLevelRegenerationGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorCarrierTangentProjectionGate

set_option autoImplicit false

structure TwoSectorCarrierTangentProjectionGate where
  sourceLevelRegenerationGatePassed : Prop
  weylProjected : Prop
  theta0Projected : Prop
  piProjected : Prop
  fullTwoSectorProjected : Prop
  parallelFractionReported : Prop
  perpendicularFractionReported : Prop
  classificationReported : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  rhoEffShortcutForbidden : Prop
  directClPatchForbidden : Prop
  rawToyLOSForbidden : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def projectionReady (g : TwoSectorCarrierTangentProjectionGate) : Prop :=
  g.sourceLevelRegenerationGatePassed /\
  g.weylProjected /\
  g.theta0Projected /\
  g.piProjected /\
  g.fullTwoSectorProjected /\
  g.parallelFractionReported /\
  g.perpendicularFractionReported /\
  g.classificationReported /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  g.rhoEffShortcutForbidden /\
  g.directClPatchForbidden /\
  g.rawToyLOSForbidden /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem two_sector_projection_is_pre_planck
    (g : TwoSectorCarrierTangentProjectionGate)
    (hPolicy : projectionReady g -> g.gatePassed)
    (h : projectionReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorCarrierTangentProjectionGate
end JanusFormal

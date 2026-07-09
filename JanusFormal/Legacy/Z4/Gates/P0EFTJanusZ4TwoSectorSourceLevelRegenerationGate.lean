import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4TwoSectorStabilityEigenmodeGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorSourceLevelRegenerationGate

set_option autoImplicit false

structure TwoSectorSourceLevelRegenerationGate where
  stabilityGatePassed : Prop
  plusSourceRegenerated : Prop
  minusSourceRegenerated : Prop
  antisymmetricZ4SourceRegenerated : Prop
  projectionSourceRegenerated : Prop
  deltaWeylPlusObservableRegenerated : Prop
  theta0TwoSectorProjectionRegenerated : Prop
  piTwoSectorProjectionRegenerated : Prop
  sourceCacheKeyIncludesTwoSectorVersion : Prop
  sourceCacheKeyIncludesProjectionHash : Prop
  sourceCacheKeyIncludesModeBasisHash : Prop
  rhoEffShortcutForbidden : Prop
  directClPatchForbidden : Prop
  rawToyLOSForbidden : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  carrierTangentProjectionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def sourceRegenerationReady (g : TwoSectorSourceLevelRegenerationGate) : Prop :=
  g.stabilityGatePassed /\
  g.plusSourceRegenerated /\
  g.minusSourceRegenerated /\
  g.antisymmetricZ4SourceRegenerated /\
  g.projectionSourceRegenerated /\
  g.deltaWeylPlusObservableRegenerated /\
  g.theta0TwoSectorProjectionRegenerated /\
  g.piTwoSectorProjectionRegenerated /\
  g.sourceCacheKeyIncludesTwoSectorVersion /\
  g.sourceCacheKeyIncludesProjectionHash /\
  g.sourceCacheKeyIncludesModeBasisHash /\
  g.rhoEffShortcutForbidden /\
  g.directClPatchForbidden /\
  g.rawToyLOSForbidden /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  g.carrierTangentProjectionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem source_regeneration_allows_tangent_projection_only
    (g : TwoSectorSourceLevelRegenerationGate)
    (hPolicy : sourceRegenerationReady g -> g.gatePassed)
    (h : sourceRegenerationReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorSourceLevelRegenerationGate
end JanusFormal

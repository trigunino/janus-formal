import JanusFormal.P0EFTJanusZ4MasterAnsatzRevisionScanGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterSourceLevelRegenerationGate

set_option autoImplicit false

structure MasterSourceLevelRegenerationGate where
  masterAnsatzRevisionScanPassed : Prop
  selectedAnsatzBelowCarrierThreshold : Prop
  uZ4Regenerated : Prop
  temperatureSourceRegeneratedFromUZ4 : Prop
  polarizationSourceRegeneratedFromUZ4 : Prop
  lensingSourceRegeneratedFromUZ4 : Prop
  dopplerRegeneratedFromUZ4 : Prop
  theta0RegeneratedFromUZ4 : Prop
  piRegeneratedFromUZ4 : Prop
  slipRegeneratedFromUZ4 : Prop
  minusSectorRegeneratedFromUZ4 : Prop
  allSourcesShareSameUZ4Hash : Prop
  independentDownstreamSourceAllowed : Prop
  lambdaRetuningAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def sourceLevelReady (g : MasterSourceLevelRegenerationGate) : Prop :=
  g.masterAnsatzRevisionScanPassed /\
  g.selectedAnsatzBelowCarrierThreshold /\
  g.uZ4Regenerated /\
  g.temperatureSourceRegeneratedFromUZ4 /\
  g.polarizationSourceRegeneratedFromUZ4 /\
  g.lensingSourceRegeneratedFromUZ4 /\
  g.dopplerRegeneratedFromUZ4 /\
  g.theta0RegeneratedFromUZ4 /\
  g.piRegeneratedFromUZ4 /\
  g.slipRegeneratedFromUZ4 /\
  g.minusSectorRegeneratedFromUZ4 /\
  g.allSourcesShareSameUZ4Hash /\
  Not g.independentDownstreamSourceAllowed /\
  Not g.lambdaRetuningAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem master_source_level_regeneration_remains_pre_observational
    (g : MasterSourceLevelRegenerationGate)
    (hPolicy : sourceLevelReady g -> g.gatePassed)
    (h : sourceLevelReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterSourceLevelRegenerationGate
end JanusFormal

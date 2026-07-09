import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MasterHighLAcousticRevisionScanGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterRevisedSourceLevelRegenerationGate

set_option autoImplicit false

structure MasterRevisedSourceLevelRegenerationGate where
  revisionScanPassed : Prop
  selectedRevisionIsUpstreamMaster : Prop
  sharedUZ4NormalizationApplied : Prop
  silkGuardAppliedUpstream : Prop
  uZ4RevisedFromSelectedRevision : Prop
  temperatureSourceRegeneratedFromRevisedUZ4 : Prop
  polarizationSourceRegeneratedFromRevisedUZ4 : Prop
  lensingSourceRegeneratedFromRevisedUZ4 : Prop
  dopplerRegeneratedFromRevisedUZ4 : Prop
  theta0RegeneratedFromRevisedUZ4 : Prop
  piRegeneratedFromRevisedUZ4 : Prop
  slipRegeneratedFromRevisedUZ4 : Prop
  minusSectorRegeneratedFromRevisedUZ4 : Prop
  allRevisedSourcesShareSameUZ4Hash : Prop
  downstreamPatchAllowed : Prop
  independentDownstreamSourceAllowed : Prop
  lambdaRetuningAllowed : Prop
  spectraGenerationAllowed : Prop
  observedPlanckRerunAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def revisedSourceReady (g : MasterRevisedSourceLevelRegenerationGate) : Prop :=
  g.revisionScanPassed /\
  g.selectedRevisionIsUpstreamMaster /\
  g.sharedUZ4NormalizationApplied /\
  g.silkGuardAppliedUpstream /\
  g.uZ4RevisedFromSelectedRevision /\
  g.temperatureSourceRegeneratedFromRevisedUZ4 /\
  g.polarizationSourceRegeneratedFromRevisedUZ4 /\
  g.lensingSourceRegeneratedFromRevisedUZ4 /\
  g.dopplerRegeneratedFromRevisedUZ4 /\
  g.theta0RegeneratedFromRevisedUZ4 /\
  g.piRegeneratedFromRevisedUZ4 /\
  g.slipRegeneratedFromRevisedUZ4 /\
  g.minusSectorRegeneratedFromRevisedUZ4 /\
  g.allRevisedSourcesShareSameUZ4Hash /\
  Not g.downstreamPatchAllowed /\
  Not g.independentDownstreamSourceAllowed /\
  Not g.lambdaRetuningAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.observedPlanckRerunAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem revised_source_level_regeneration_stays_pre_observational
    (g : MasterRevisedSourceLevelRegenerationGate)
    (hPolicy : revisedSourceReady g -> g.gatePassed)
    (h : revisedSourceReady g) :
    g.gatePassed /\ Not g.observedPlanckRerunAllowed := by
  have hGate : g.gatePassed := hPolicy h
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNoRerun, _, _, _⟩
  exact And.intro hGate hNoRerun

end P0EFTJanusZ4MasterRevisedSourceLevelRegenerationGate
end JanusFormal

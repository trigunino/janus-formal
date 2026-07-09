import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4MinusSectorMicrophysicsSpecificationGate

namespace JanusFormal
namespace P0EFTJanusZ4MinusSectorSoundSpeedJeansGate

set_option autoImplicit false

structure MinusSectorSoundSpeedJeansGate where
  microphysicsSpecificationPassed : Prop
  soundSpeedDiffersFromPlus : Prop
  pressureDiffersFromPlus : Prop
  jeansScaleDeclared : Prop
  residualAfterAmplitudeFitReported : Prop
  effectiveTransferRankReported : Prop
  carrierTangentProjectionReported : Prop
  derivedFromFullAction : Prop
  freeMinusAmplitudeAllowed : Prop
  rhoEffShortcutAllowed : Prop
  projectionOnlyFixAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def jeansAuditReady (g : MinusSectorSoundSpeedJeansGate) : Prop :=
  g.microphysicsSpecificationPassed /\
  g.soundSpeedDiffersFromPlus /\
  g.pressureDiffersFromPlus /\
  g.jeansScaleDeclared /\
  g.residualAfterAmplitudeFitReported /\
  g.effectiveTransferRankReported /\
  g.carrierTangentProjectionReported /\
  Not g.derivedFromFullAction /\
  Not g.freeMinusAmplitudeAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.projectionOnlyFixAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem sound_speed_jeans_gate_is_pre_observational
    (g : MinusSectorSoundSpeedJeansGate)
    (hPolicy : jeansAuditReady g -> g.gatePassed)
    (h : jeansAuditReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MinusSectorSoundSpeedJeansGate
end JanusFormal

import JanusFormal.P0EFTJanusZ4MinusSectorShearFreeStreamingGate

namespace JanusFormal
namespace P0EFTJanusZ4MinusSectorThermalRatioGate

set_option autoImplicit false

structure MinusSectorThermalRatioGate where
  shearFreeStreamingGateCompleted : Prop
  thermalRatioDeclared : Prop
  pressureModificationAudited : Prop
  dampingScaleAudited : Prop
  decouplingTimingProxyAudited : Prop
  piResponseAudited : Prop
  fullChannelAudited : Prop
  transferRankReported : Prop
  carrierTangentFractionReported : Prop
  derivedFromFullAction : Prop
  freeThermalRatioFitAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def thermalAuditReady (g : MinusSectorThermalRatioGate) : Prop :=
  g.shearFreeStreamingGateCompleted /\
  g.thermalRatioDeclared /\
  g.pressureModificationAudited /\
  g.dampingScaleAudited /\
  g.decouplingTimingProxyAudited /\
  g.piResponseAudited /\
  g.fullChannelAudited /\
  g.transferRankReported /\
  g.carrierTangentFractionReported /\
  Not g.derivedFromFullAction /\
  Not g.freeThermalRatioFitAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem thermal_ratio_gate_is_pre_observational
    (g : MinusSectorThermalRatioGate)
    (hPolicy : thermalAuditReady g -> g.gatePassed)
    (h : thermalAuditReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MinusSectorThermalRatioGate
end JanusFormal

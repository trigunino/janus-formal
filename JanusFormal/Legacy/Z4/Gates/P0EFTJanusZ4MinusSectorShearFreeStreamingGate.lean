import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MinusSectorSoundSpeedJeansGate

namespace JanusFormal
namespace P0EFTJanusZ4MinusSectorShearFreeStreamingGate

set_option autoImplicit false

structure MinusSectorShearFreeStreamingGate where
  soundSpeedJeansGateCompleted : Prop
  sigmaMinusDeclared : Prop
  flMinusHierarchyDeclared : Prop
  shearOnlyAudited : Prop
  freeStreamingOnlyAudited : Prop
  weylAnisotropicStressAudited : Prop
  piResponseAudited : Prop
  fullChannelAudited : Prop
  conservationBianchiEnforced : Prop
  transferRankReported : Prop
  carrierTangentFractionReported : Prop
  derivedFromFullAction : Prop
  freeShearAmplitudeAllowed : Prop
  freeStreamingAmplitudeAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def shearAuditReady (g : MinusSectorShearFreeStreamingGate) : Prop :=
  g.soundSpeedJeansGateCompleted /\
  g.sigmaMinusDeclared /\
  g.flMinusHierarchyDeclared /\
  g.shearOnlyAudited /\
  g.freeStreamingOnlyAudited /\
  g.weylAnisotropicStressAudited /\
  g.piResponseAudited /\
  g.fullChannelAudited /\
  g.conservationBianchiEnforced /\
  g.transferRankReported /\
  g.carrierTangentFractionReported /\
  Not g.derivedFromFullAction /\
  Not g.freeShearAmplitudeAllowed /\
  Not g.freeStreamingAmplitudeAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem shear_free_streaming_gate_is_pre_observational
    (g : MinusSectorShearFreeStreamingGate)
    (hPolicy : shearAuditReady g -> g.gatePassed)
    (h : shearAuditReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MinusSectorShearFreeStreamingGate
end JanusFormal

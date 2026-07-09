import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4DerivedSlipPhotonMonopoleSWClosureGate

namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipSurfaceDopplerDecompositionGate

set_option autoImplicit false

structure DerivedSlipSurfaceDopplerDecompositionGate where
  swOnlyParallelReported : Prop
  dopplerOnlyParallelReported : Prop
  fullSurfaceParallelReported : Prop
  crossTermAlignmentReported : Prop
  dopplerReintroducesCarrierTangency : Prop
  swSurfacePromising : Prop
  planckTrialAllowed : Prop
  candidatePromotionAllowed : Prop
  noLambdaRetuning : Prop
  noFreeDopplerAmplitude : Prop
  noFreeSlipParameter : Prop
  noFreeEtaRatio : Prop
  noDirectClPatch : Prop
  rawToyLOSForbidden : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def decompositionReady (g : DerivedSlipSurfaceDopplerDecompositionGate) : Prop :=
  g.swOnlyParallelReported /\
  g.dopplerOnlyParallelReported /\
  g.fullSurfaceParallelReported /\
  g.crossTermAlignmentReported /\
  g.dopplerReintroducesCarrierTangency /\
  g.swSurfacePromising /\
  Not g.planckTrialAllowed /\
  Not g.candidatePromotionAllowed /\
  g.noLambdaRetuning /\
  g.noFreeDopplerAmplitude /\
  g.noFreeSlipParameter /\
  g.noFreeEtaRatio /\
  g.noDirectClPatch /\
  g.rawToyLOSForbidden /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem doppler_decomposition_is_diagnostic_only
    (g : DerivedSlipSurfaceDopplerDecompositionGate)
    (hPolicy : decompositionReady g -> g.gatePassed)
    (h : decompositionReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipSurfaceDopplerDecompositionGate
end JanusFormal

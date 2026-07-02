import JanusFormal.P0EFTJanusZ4DerivedSlipSurfaceDopplerDecompositionGate

namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipSurfaceCarrierTangentProjectionGate

set_option autoImplicit false

structure DerivedSlipSurfaceCarrierTangentProjectionGate where
  fullSurfaceParallelReported : Prop
  thresholdPolicyDeclared : Prop
  weakOrthogonalDiagnostic : Prop
  dopplerReintroducesCarrierTangency : Prop
  candidatePromotionAllowed : Prop
  planckTrialAllowed : Prop
  diagnosticSurfaceTrialAllowed : Prop
  noLambdaRetuning : Prop
  noFreeDopplerAmplitude : Prop
  noFreeSlipParameter : Prop
  noFreeEtaRatio : Prop
  noDirectClPatch : Prop
  rawToyLOSForbidden : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def weakDiagnosticReady (g : DerivedSlipSurfaceCarrierTangentProjectionGate) : Prop :=
  g.fullSurfaceParallelReported /\
  g.thresholdPolicyDeclared /\
  g.weakOrthogonalDiagnostic /\
  g.dopplerReintroducesCarrierTangency /\
  Not g.candidatePromotionAllowed /\
  Not g.planckTrialAllowed /\
  Not g.diagnosticSurfaceTrialAllowed /\
  g.noLambdaRetuning /\
  g.noFreeDopplerAmplitude /\
  g.noFreeSlipParameter /\
  g.noFreeEtaRatio /\
  g.noDirectClPatch /\
  g.rawToyLOSForbidden /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem weak_surface_branch_blocks_planck_trial
    (g : DerivedSlipSurfaceCarrierTangentProjectionGate)
    (hPolicy : weakDiagnosticReady g -> g.gatePassed)
    (h : weakDiagnosticReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipSurfaceCarrierTangentProjectionGate
end JanusFormal

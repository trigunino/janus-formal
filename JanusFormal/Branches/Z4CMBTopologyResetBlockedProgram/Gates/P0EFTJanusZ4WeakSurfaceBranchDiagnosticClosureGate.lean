import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4DopplerTransportClosureRefinementGate

namespace JanusFormal
namespace P0EFTJanusZ4WeakSurfaceBranchDiagnosticClosureGate

set_option autoImplicit false

structure WeakSurfaceBranchDiagnosticClosureGate where
  swSurfaceOrthogonalComponentExists : Prop
  physicalDopplerCompletedSurfaceCarrierTangent : Prop
  closeWeakSurfaceBranch : Prop
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

def weakSurfaceDiagnosticClosureReady
    (g : WeakSurfaceBranchDiagnosticClosureGate) : Prop :=
  g.swSurfaceOrthogonalComponentExists /\
  g.physicalDopplerCompletedSurfaceCarrierTangent /\
  g.closeWeakSurfaceBranch /\
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

theorem weak_surface_branch_closure_blocks_trials
    (g : WeakSurfaceBranchDiagnosticClosureGate)
    (hPolicy : weakSurfaceDiagnosticClosureReady g -> g.gatePassed)
    (h : weakSurfaceDiagnosticClosureReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4WeakSurfaceBranchDiagnosticClosureGate
end JanusFormal

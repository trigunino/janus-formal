import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DopplerTransportClosureRefinementGate

namespace JanusFormal
namespace P0EFTJanusZ4WeakSurfaceBranchArchiveGate

set_option autoImplicit false

structure WeakSurfaceBranchArchiveGate where
  swSurfaceOrthogonalComponentExists : Prop
  physicalDopplerCompletedSurfaceCarrierTangent : Prop
  archiveWeakSurfaceBranch : Prop
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

def archiveReady (g : WeakSurfaceBranchArchiveGate) : Prop :=
  g.swSurfaceOrthogonalComponentExists /\
  g.physicalDopplerCompletedSurfaceCarrierTangent /\
  g.archiveWeakSurfaceBranch /\
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

theorem weak_surface_branch_archive_blocks_trials
    (g : WeakSurfaceBranchArchiveGate)
    (hPolicy : archiveReady g -> g.gatePassed)
    (h : archiveReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4WeakSurfaceBranchArchiveGate
end JanusFormal

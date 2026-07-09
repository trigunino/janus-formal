import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4RegenerativePolarizationPiSourceGate

namespace JanusFormal
namespace P0EFTJanusZ4StrictSourceLevelFrozenCandidateReplayGate

set_option autoImplicit false

structure StrictSourceLevelFrozenCandidateReplayGate where
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  deltaSTZ4RegeneratedPerCosmology : Prop
  piSourceZ4RegeneratedPerCosmology : Prop
  photonPolarizationHierarchyRegeneratedPerCosmology : Prop
  sourceLevelZ4DeltasRegeneratedPerCosmology : Prop
  checkpointReplayMatches : Prop
  teCostSmall : Prop
  eeNonDegraded : Prop
  nonOverlapAccountingOnly : Prop
  transportGuardsPass : Prop
  tcaLmaxGuardsPass : Prop
  localCosmologyProfilingAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def strictReplayReady (g : StrictSourceLevelFrozenCandidateReplayGate) : Prop :=
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.deltaSTZ4RegeneratedPerCosmology /\
  g.piSourceZ4RegeneratedPerCosmology /\
  g.photonPolarizationHierarchyRegeneratedPerCosmology /\
  g.sourceLevelZ4DeltasRegeneratedPerCosmology /\
  g.checkpointReplayMatches /\
  g.teCostSmall /\
  g.eeNonDegraded /\
  g.nonOverlapAccountingOnly /\
  g.transportGuardsPass /\
  g.tcaLmaxGuardsPass /\
  Not g.localCosmologyProfilingAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem strict_replay_ready_passes_gate
    (g : StrictSourceLevelFrozenCandidateReplayGate)
    (hPolicy : strictReplayReady g -> g.gatePassed)
    (h : strictReplayReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4StrictSourceLevelFrozenCandidateReplayGate
end JanusFormal

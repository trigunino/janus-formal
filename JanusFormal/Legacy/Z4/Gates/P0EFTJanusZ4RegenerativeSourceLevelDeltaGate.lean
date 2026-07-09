import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4RegenerativeZ4DeltaPerCosmologyGate

namespace JanusFormal
namespace P0EFTJanusZ4RegenerativeSourceLevelDeltaGate

set_option autoImplicit false

structure RegenerativeSourceLevelDeltaGate where
  effectiveGatePassed : Prop
  lambdaFrozen : Prop
  noNewPhysics : Prop
  noLambdaRetuning : Prop
  deltaSTZ4RegeneratedPerCosmology : Prop
  piSourceRegeneratedPerCosmology : Prop
  photonPolarizationHierarchySourceRegeneratedPerCosmology : Prop
  sourceDeltaCacheKeyIncludesCosmologyHash : Prop
  sourceDeltaCacheKeyIncludesLambdaHash : Prop
  noStaleSourceDeltaReuse : Prop
  fullSourceLevelZ4DeltaRegeneration : Prop
  localCosmologyProfilingAllowed : Prop
  strictSourceLevelGatePassed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def strictSourceReady (g : RegenerativeSourceLevelDeltaGate) : Prop :=
  g.effectiveGatePassed /\
  g.lambdaFrozen /\
  g.noNewPhysics /\
  g.noLambdaRetuning /\
  g.deltaSTZ4RegeneratedPerCosmology /\
  g.piSourceRegeneratedPerCosmology /\
  g.photonPolarizationHierarchySourceRegeneratedPerCosmology /\
  g.sourceDeltaCacheKeyIncludesCosmologyHash /\
  g.sourceDeltaCacheKeyIncludesLambdaHash /\
  g.noStaleSourceDeltaReuse /\
  g.fullSourceLevelZ4DeltaRegeneration /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem strict_source_ready_passes_gate
    (g : RegenerativeSourceLevelDeltaGate)
    (hPolicy : strictSourceReady g -> g.strictSourceLevelGatePassed)
    (h : strictSourceReady g) :
    g.strictSourceLevelGatePassed := by
  exact hPolicy h

theorem missing_delta_ST_blocks_strict_source
    (g : RegenerativeSourceLevelDeltaGate)
    (hMissing : Not g.deltaSTZ4RegeneratedPerCosmology) :
    Not (strictSourceReady g) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0EFTJanusZ4RegenerativeSourceLevelDeltaGate
end JanusFormal

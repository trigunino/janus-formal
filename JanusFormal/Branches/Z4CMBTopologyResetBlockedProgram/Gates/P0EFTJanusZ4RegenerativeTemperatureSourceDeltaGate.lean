import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4RegenerativeSourceLevelDeltaGate

namespace JanusFormal
namespace P0EFTJanusZ4RegenerativeTemperatureSourceDeltaGate

set_option autoImplicit false

structure RegenerativeTemperatureSourceDeltaGate where
  lambdaFrozen : Prop
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  sourceDeltaCacheKeyIncludesCosmologyHash : Prop
  sourceDeltaCacheKeyIncludesLambdaHash : Prop
  wAcousticRegeneratedPerCosmology : Prop
  kappaRegeneratedPerCosmology : Prop
  deltaPhiDotPlusDeltaPsiDotRegeneratedPerCosmology : Prop
  timeGridRegeneratedPerCosmology : Prop
  projectionGridRegeneratedPerCosmology : Prop
  deltaSTZ4RegeneratedPerCosmology : Prop
  noStaleTemperatureSourceReuse : Prop
  localCosmologyProfilingAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def temperatureSourceReady (g : RegenerativeTemperatureSourceDeltaGate) : Prop :=
  g.lambdaFrozen /\
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.sourceDeltaCacheKeyIncludesCosmologyHash /\
  g.sourceDeltaCacheKeyIncludesLambdaHash /\
  g.wAcousticRegeneratedPerCosmology /\
  g.kappaRegeneratedPerCosmology /\
  g.deltaPhiDotPlusDeltaPsiDotRegeneratedPerCosmology /\
  g.timeGridRegeneratedPerCosmology /\
  g.projectionGridRegeneratedPerCosmology /\
  g.deltaSTZ4RegeneratedPerCosmology /\
  g.noStaleTemperatureSourceReuse /\
  Not g.localCosmologyProfilingAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem temperature_source_ready_passes_gate
    (g : RegenerativeTemperatureSourceDeltaGate)
    (hPolicy : temperatureSourceReady g -> g.gatePassed)
    (h : temperatureSourceReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4RegenerativeTemperatureSourceDeltaGate
end JanusFormal

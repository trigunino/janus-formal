import JanusFormal.P0EFTJanusZ4RegenerativeTemperatureSourceDeltaGate

namespace JanusFormal
namespace P0EFTJanusZ4RegenerativePolarizationPiSourceGate

set_option autoImplicit false

structure RegenerativePolarizationPiSourceGate where
  lambdaFrozen : Prop
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  thetaLRegeneratedPerCosmology : Prop
  eLRegeneratedPerCosmology : Prop
  piSourceRegeneratedPerCosmology : Prop
  photonPolarizationHierarchyRegeneratedPerCosmology : Prop
  tcaSwitchRegeneratedPerCosmology : Prop
  opacityDependenceRegeneratedPerCosmology : Prop
  timeGridRegeneratedPerCosmology : Prop
  piSourceDerivedFromMultipoles : Prop
  noFreeTheta2SourceTag : Prop
  noDirectEEPatch : Prop
  noDirectTEPatch : Prop
  sourceDeltaCacheKeyIncludesCosmologyHash : Prop
  sourceDeltaCacheKeyIncludesLambdaHash : Prop
  hierarchyLmaxIncludedInCacheKey : Prop
  tcaSettingsHashIncludedInCacheKey : Prop
  opacityGridHashIncludedInCacheKey : Prop
  noStalePiSourceReuse : Prop
  localCosmologyProfilingAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def polarizationPiReady (g : RegenerativePolarizationPiSourceGate) : Prop :=
  g.lambdaFrozen /\
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.thetaLRegeneratedPerCosmology /\
  g.eLRegeneratedPerCosmology /\
  g.piSourceRegeneratedPerCosmology /\
  g.photonPolarizationHierarchyRegeneratedPerCosmology /\
  g.tcaSwitchRegeneratedPerCosmology /\
  g.opacityDependenceRegeneratedPerCosmology /\
  g.timeGridRegeneratedPerCosmology /\
  g.piSourceDerivedFromMultipoles /\
  g.noFreeTheta2SourceTag /\
  g.noDirectEEPatch /\
  g.noDirectTEPatch /\
  g.sourceDeltaCacheKeyIncludesCosmologyHash /\
  g.sourceDeltaCacheKeyIncludesLambdaHash /\
  g.hierarchyLmaxIncludedInCacheKey /\
  g.tcaSettingsHashIncludedInCacheKey /\
  g.opacityGridHashIncludedInCacheKey /\
  g.noStalePiSourceReuse /\
  Not g.localCosmologyProfilingAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem polarization_pi_ready_passes_gate
    (g : RegenerativePolarizationPiSourceGate)
    (hPolicy : polarizationPiReady g -> g.gatePassed)
    (h : polarizationPiReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4RegenerativePolarizationPiSourceGate
end JanusFormal

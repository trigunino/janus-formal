import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4DerivedSlipValueTransportGate

namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipSourceLevelRegenerationGate

set_option autoImplicit false

structure DerivedSlipSourceLevelRegenerationGate where
  deltaSlipValueAvailable : Prop
  deltaSlipDotAvailable : Prop
  visibleSlipProjectionDeclared : Prop
  dirichletBoundaryValueZeroLogged : Prop
  normalDerivativeProjectionNonzeroLogged : Prop
  normalOrientationSignDeclared : Prop
  sourceLevelCacheKeyIncludesSlipKernelHash : Prop
  deltaPhiReconstructed : Prop
  deltaPsiReconstructed : Prop
  temperatureSurfaceTermRegeneratedWithSlip : Prop
  temperatureEarlyISWTermRegeneratedWithSlip : Prop
  temperatureSourceRegeneratedWithSlip : Prop
  piSourceRegeneratedWithSlip : Prop
  photonPolarizationHierarchyRegeneratedWithSlip : Prop
  fullSlipSourceRegenerated : Prop
  grLimitSlipZero : Prop
  noFreeSlipParameter : Prop
  noFreeEtaRatio : Prop
  noDirectClPatch : Prop
  rawToyLOSForbidden : Prop
  planckTrialAllowed : Prop
  localCosmologyProfilingAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def sourceLevelSlipReady (g : DerivedSlipSourceLevelRegenerationGate) : Prop :=
  g.deltaSlipValueAvailable /\
  g.deltaSlipDotAvailable /\
  g.visibleSlipProjectionDeclared /\
  g.dirichletBoundaryValueZeroLogged /\
  g.normalDerivativeProjectionNonzeroLogged /\
  g.normalOrientationSignDeclared /\
  g.sourceLevelCacheKeyIncludesSlipKernelHash /\
  g.deltaPhiReconstructed /\
  g.deltaPsiReconstructed /\
  g.temperatureSurfaceTermRegeneratedWithSlip /\
  g.temperatureEarlyISWTermRegeneratedWithSlip /\
  g.temperatureSourceRegeneratedWithSlip /\
  g.piSourceRegeneratedWithSlip /\
  g.photonPolarizationHierarchyRegeneratedWithSlip /\
  g.fullSlipSourceRegenerated /\
  g.grLimitSlipZero /\
  g.noFreeSlipParameter /\
  g.noFreeEtaRatio /\
  g.noDirectClPatch /\
  g.rawToyLOSForbidden /\
  Not g.planckTrialAllowed /\
  Not g.localCosmologyProfilingAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem regenerated_sources_with_derived_slip_pass_gate
    (g : DerivedSlipSourceLevelRegenerationGate)
    (hPolicy : sourceLevelSlipReady g -> g.gatePassed)
    (h : sourceLevelSlipReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipSourceLevelRegenerationGate
end JanusFormal

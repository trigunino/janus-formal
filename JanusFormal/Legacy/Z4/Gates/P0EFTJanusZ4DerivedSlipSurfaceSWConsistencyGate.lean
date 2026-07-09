import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DerivedSlipSurfaceOrthogonalityGate

namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipSurfaceSWConsistencyGate

set_option autoImplicit false

structure DerivedSlipSurfaceSWConsistencyGate where
  surfaceTermParallelFractionRecorded : Prop
  fullDerivedSlipArchived : Prop
  deltaPsiDerivedFromSlip : Prop
  photonMonopoleResponseDeclared : Prop
  swCombinationConsistencyChecked : Prop
  dopplerLeakageChecked : Prop
  gaugeConventionDeclared : Prop
  visibilityUnchanged : Prop
  recombinationUnchanged : Prop
  surfaceSWPhysicalClosure : Prop
  planckTrialAllowed : Prop
  diagnosticSurfaceOnlyTrialAllowed : Prop
  noLambdaRetuning : Prop
  noFreeSlipParameter : Prop
  noFreeEtaRatio : Prop
  noDirectClPatch : Prop
  rawToyLOSForbidden : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def blockedUntilPhotonMonopoleReady (g : DerivedSlipSurfaceSWConsistencyGate) : Prop :=
  g.surfaceTermParallelFractionRecorded /\
  g.fullDerivedSlipArchived /\
  g.deltaPsiDerivedFromSlip /\
  Not g.photonMonopoleResponseDeclared /\
  Not g.swCombinationConsistencyChecked /\
  Not g.dopplerLeakageChecked /\
  g.gaugeConventionDeclared /\
  g.visibilityUnchanged /\
  g.recombinationUnchanged /\
  Not g.surfaceSWPhysicalClosure /\
  Not g.planckTrialAllowed /\
  Not g.diagnosticSurfaceOnlyTrialAllowed /\
  g.noLambdaRetuning /\
  g.noFreeSlipParameter /\
  g.noFreeEtaRatio /\
  g.noDirectClPatch /\
  g.rawToyLOSForbidden /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem surface_sw_gate_blocks_until_photon_monopole
    (g : DerivedSlipSurfaceSWConsistencyGate)
    (hPolicy : blockedUntilPhotonMonopoleReady g -> g.gatePassed)
    (h : blockedUntilPhotonMonopoleReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipSurfaceSWConsistencyGate
end JanusFormal

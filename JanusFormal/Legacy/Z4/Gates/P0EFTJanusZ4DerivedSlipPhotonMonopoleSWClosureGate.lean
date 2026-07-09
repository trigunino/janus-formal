import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DerivedSlipSurfaceSWConsistencyGate

namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipPhotonMonopoleSWClosureGate

set_option autoImplicit false

structure DerivedSlipPhotonMonopoleSWClosureGate where
  deltaPsiFromDerivedSlip : Prop
  deltaPhiFromDerivedSlip : Prop
  photonMonopoleResponseDeclared : Prop
  deltaTheta0Free : Prop
  dopplerResponseDeclared : Prop
  dopplerFree : Prop
  surfaceSWSourceDeclared : Prop
  fullSurfaceSourceDeclared : Prop
  gaugeConventionDeclared : Prop
  visibilityFrozen : Prop
  recombinationFrozen : Prop
  tightCouplingPolicyDeclared : Prop
  potentialOnlyParallelFractionReported : Prop
  monopolePlusPotentialParallelFractionReported : Prop
  fullSurfaceParallelFractionReported : Prop
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

def swClosureReady (g : DerivedSlipPhotonMonopoleSWClosureGate) : Prop :=
  g.deltaPsiFromDerivedSlip /\
  g.deltaPhiFromDerivedSlip /\
  g.photonMonopoleResponseDeclared /\
  Not g.deltaTheta0Free /\
  g.dopplerResponseDeclared /\
  Not g.dopplerFree /\
  g.surfaceSWSourceDeclared /\
  g.fullSurfaceSourceDeclared /\
  g.gaugeConventionDeclared /\
  g.visibilityFrozen /\
  g.recombinationFrozen /\
  g.tightCouplingPolicyDeclared /\
  g.potentialOnlyParallelFractionReported /\
  g.monopolePlusPotentialParallelFractionReported /\
  g.fullSurfaceParallelFractionReported /\
  Not g.planckTrialAllowed /\
  Not g.diagnosticSurfaceOnlyTrialAllowed /\
  g.noLambdaRetuning /\
  g.noFreeSlipParameter /\
  g.noFreeEtaRatio /\
  g.noDirectClPatch /\
  g.rawToyLOSForbidden /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem photon_monopole_sw_closure_remains_pre_planck
    (g : DerivedSlipPhotonMonopoleSWClosureGate)
    (hPolicy : swClosureReady g -> g.gatePassed)
    (h : swClosureReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipPhotonMonopoleSWClosureGate
end JanusFormal

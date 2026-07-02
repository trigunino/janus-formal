import JanusFormal.P0EFTJanusZ4DerivedSlipSurfaceCarrierTangentProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ4DopplerTransportClosureRefinementGate

set_option autoImplicit false

structure DopplerTransportClosureRefinementGate where
  photonDipoleResponseDerived : Prop
  baryonVelocityResponseDerived : Prop
  eulerContinuityConsistency : Prop
  tightCouplingConsistency : Prop
  gaugeConventionFixed : Prop
  visibilityFrozen : Prop
  recombinationFrozen : Prop
  noFreeDopplerAmplitude : Prop
  noDirectClPatch : Prop
  refinedFractionsReported : Prop
  branchStatusReported : Prop
  planckTrialAllowed : Prop
  diagnosticSurfaceTrialAllowed : Prop
  noLambdaRetuning : Prop
  noFreeSlipParameter : Prop
  noFreeEtaRatio : Prop
  rawToyLOSForbidden : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def refinementReady (g : DopplerTransportClosureRefinementGate) : Prop :=
  g.photonDipoleResponseDerived /\
  g.baryonVelocityResponseDerived /\
  g.eulerContinuityConsistency /\
  g.tightCouplingConsistency /\
  g.gaugeConventionFixed /\
  g.visibilityFrozen /\
  g.recombinationFrozen /\
  g.noFreeDopplerAmplitude /\
  g.noDirectClPatch /\
  g.refinedFractionsReported /\
  g.branchStatusReported /\
  Not g.planckTrialAllowed /\
  Not g.diagnosticSurfaceTrialAllowed /\
  g.noLambdaRetuning /\
  g.noFreeSlipParameter /\
  g.noFreeEtaRatio /\
  g.rawToyLOSForbidden /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem doppler_refinement_remains_pre_planck
    (g : DopplerTransportClosureRefinementGate)
    (hPolicy : refinementReady g -> g.gatePassed)
    (h : refinementReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DopplerTransportClosureRefinementGate
end JanusFormal

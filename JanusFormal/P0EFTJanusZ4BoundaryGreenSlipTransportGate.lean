namespace JanusFormal
namespace P0EFTJanusZ4BoundaryGreenSlipTransportGate

set_option autoImplicit false

structure BoundaryGreenSlipTransportGate where
  slipSourceEquationAvailable : Prop
  greenKernelDeclared : Prop
  greenKernelDerived : Prop
  retardedCausalSupport : Prop
  boundaryConditionsDeclared : Prop
  normalizationFixed : Prop
  grLimitSlipZero : Prop
  noArbitraryHomogeneousMode : Prop
  regularKToZero : Prop
  regularLargeK : Prop
  bianchiResidualGuard : Prop
  greenKernelFinite : Prop
  boundaryJumpConditionsSatisfied : Prop
  slipValueTransportAvailable : Prop
  deltaSlipValueAvailable : Prop
  deltaSlipDotAvailable : Prop
  deltaPhiReconstructed : Prop
  deltaPsiReconstructed : Prop
  sourceLevelSlipRegenerationPossible : Prop
  freeSlipParameter : Prop
  freeEtaRatio : Prop
  directClPatch : Prop
  rawToyLOS : Prop
  lambdaRetuning : Prop
  planckTrialAllowed : Prop
  boundaryGreenSlipTransportGatePassed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def boundaryGreenBlockedUntilKernelDerived (g : BoundaryGreenSlipTransportGate) : Prop :=
  g.slipSourceEquationAvailable /\
  g.greenKernelDeclared /\
  Not g.greenKernelDerived /\
  Not g.retardedCausalSupport /\
  g.boundaryConditionsDeclared /\
  Not g.normalizationFixed /\
  g.grLimitSlipZero /\
  Not g.noArbitraryHomogeneousMode /\
  Not g.regularKToZero /\
  Not g.regularLargeK /\
  g.bianchiResidualGuard /\
  Not g.greenKernelFinite /\
  Not g.boundaryJumpConditionsSatisfied /\
  Not g.slipValueTransportAvailable /\
  Not g.deltaSlipValueAvailable /\
  Not g.deltaSlipDotAvailable /\
  Not g.deltaPhiReconstructed /\
  Not g.deltaPsiReconstructed /\
  Not g.sourceLevelSlipRegenerationPossible /\
  Not g.freeSlipParameter /\
  Not g.freeEtaRatio /\
  Not g.directClPatch /\
  Not g.rawToyLOS /\
  Not g.lambdaRetuning /\
  Not g.planckTrialAllowed /\
  Not g.boundaryGreenSlipTransportGatePassed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem boundary_green_route_stays_blocked_without_kernel
    (g : BoundaryGreenSlipTransportGate)
    (hPolicy : boundaryGreenBlockedUntilKernelDerived g -> Not g.boundaryGreenSlipTransportGatePassed)
    (h : boundaryGreenBlockedUntilKernelDerived g) :
    Not g.boundaryGreenSlipTransportGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4BoundaryGreenSlipTransportGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ4BoundaryNormalGreenKernelSolutionGate

set_option autoImplicit false

structure BoundaryNormalGreenKernelSolutionGate where
  greenEquationSolved : Prop
  boundaryJumpConditionsSatisfied : Prop
  normalizationFixed : Prop
  homogeneousModeRemoved : Prop
  kZeroRegular : Prop
  largeKRegular : Prop
  grLimitSlipZero : Prop
  bianchiResidualGuard : Prop
  gaugeConventionDeclared : Prop
  freeSlipParameter : Prop
  freeEtaRatio : Prop
  manualDeltaSlipTable : Prop
  directClPatch : Prop
  rawToyLOS : Prop
  planckTrialAllowed : Prop
  greenKernelDerived : Prop
  deltaSlipValueTransportAvailable : Prop
  deltaSlipDotAvailable : Prop
  deltaPhiDeltaPsiReconstructionAllowed : Prop
  sourceLevelSlipRegenerationPossible : Prop
  boundaryNormalGreenKernelSolutionGatePassed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def greenKernelSolutionReady (g : BoundaryNormalGreenKernelSolutionGate) : Prop :=
  g.greenEquationSolved /\
  g.boundaryJumpConditionsSatisfied /\
  g.normalizationFixed /\
  g.homogeneousModeRemoved /\
  g.kZeroRegular /\
  g.largeKRegular /\
  g.grLimitSlipZero /\
  g.bianchiResidualGuard /\
  g.gaugeConventionDeclared /\
  Not g.freeSlipParameter /\
  Not g.freeEtaRatio /\
  Not g.manualDeltaSlipTable /\
  Not g.directClPatch /\
  Not g.rawToyLOS /\
  Not g.planckTrialAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem solved_green_kernel_enables_value_transport_without_planck
    (g : BoundaryNormalGreenKernelSolutionGate)
    (hPolicy :
      greenKernelSolutionReady g ->
        g.greenKernelDerived /\
        g.deltaSlipValueTransportAvailable /\
        g.deltaSlipDotAvailable /\
        g.deltaPhiDeltaPsiReconstructionAllowed /\
        g.sourceLevelSlipRegenerationPossible /\
        g.boundaryNormalGreenKernelSolutionGatePassed)
    (h : greenKernelSolutionReady g) :
      g.greenKernelDerived /\
      g.deltaSlipValueTransportAvailable /\
      g.deltaSlipDotAvailable /\
      g.deltaPhiDeltaPsiReconstructionAllowed /\
      g.sourceLevelSlipRegenerationPossible /\
      g.boundaryNormalGreenKernelSolutionGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4BoundaryNormalGreenKernelSolutionGate
end JanusFormal

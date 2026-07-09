namespace JanusFormal
namespace P0EFTJanusZ4SlipTransportKernelGate

set_option autoImplicit false

structure SlipTransportKernelGate where
  slipSourceEquationAvailable : Prop
  boundaryGreenKernelDerived : Prop
  normalModeTransportDerived : Prop
  slipValueTransportAvailable : Prop
  deltaSlipValueAvailable : Prop
  deltaSlipDotAvailable : Prop
  deltaPhiReconstructed : Prop
  deltaPsiReconstructed : Prop
  sourceLevelRegenerationPossible : Prop
  freeSlipParameter : Prop
  freeEtaRatio : Prop
  boundaryConditionsDeclared : Prop
  normalizationFixed : Prop
  grLimitSlipZero : Prop
  bianchiResidualChecked : Prop
  gaugeConventionDeclared : Prop
  superhorizonRegular : Prop
  subhorizonRegular : Prop
  noDirectClPatch : Prop
  rawToyLOSForbidden : Prop
  planckTrialForbidden : Prop
  transportKernelGatePassed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def transportBlockedUntilKernelDerived (g : SlipTransportKernelGate) : Prop :=
  g.slipSourceEquationAvailable /\
  Not g.boundaryGreenKernelDerived /\
  Not g.normalModeTransportDerived /\
  Not g.slipValueTransportAvailable /\
  Not g.deltaSlipValueAvailable /\
  Not g.deltaSlipDotAvailable /\
  Not g.deltaPhiReconstructed /\
  Not g.deltaPsiReconstructed /\
  Not g.sourceLevelRegenerationPossible /\
  Not g.freeSlipParameter /\
  Not g.freeEtaRatio /\
  g.boundaryConditionsDeclared /\
  Not g.normalizationFixed /\
  g.grLimitSlipZero /\
  g.bianchiResidualChecked /\
  g.gaugeConventionDeclared /\
  Not g.superhorizonRegular /\
  Not g.subhorizonRegular /\
  g.noDirectClPatch /\
  g.rawToyLOSForbidden /\
  g.planckTrialForbidden /\
  Not g.transportKernelGatePassed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem slip_transport_remains_blocked_without_green_or_normal_modes
    (g : SlipTransportKernelGate)
    (hPolicy : transportBlockedUntilKernelDerived g -> Not g.transportKernelGatePassed)
    (h : transportBlockedUntilKernelDerived g) :
    Not g.transportKernelGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4SlipTransportKernelGate
end JanusFormal

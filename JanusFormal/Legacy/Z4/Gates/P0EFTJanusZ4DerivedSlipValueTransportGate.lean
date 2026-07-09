namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipValueTransportGate

set_option autoImplicit false

structure DerivedSlipValueTransportGate where
  greenKernelFromPreviousGateUsed : Prop
  projectionToVisibleSectorDeclared : Prop
  boundaryValueZeroIfDirichlet : Prop
  boundaryNormalDerivativeProjection : Prop
  deltaSlipValueAvailable : Prop
  deltaSlipDotAvailable : Prop
  visibleSlipNonzero : Prop
  kZeroLimitFinite : Prop
  largeKDecayOrBound : Prop
  sourceToValueLinearityCheck : Prop
  normalizationInheritedFromGreenKernel : Prop
  homogeneousModeNotReintroduced : Prop
  grLimitSlipZero : Prop
  freeSlipAmplitude : Prop
  freeEtaRatio : Prop
  manualDeltaSlipTable : Prop
  directClPatch : Prop
  rawToyLOS : Prop
  planckTrialAllowed : Prop
  derivedSlipValueTransportGatePassed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def valueTransportReady (g : DerivedSlipValueTransportGate) : Prop :=
  g.greenKernelFromPreviousGateUsed /\
  g.projectionToVisibleSectorDeclared /\
  g.boundaryValueZeroIfDirichlet /\
  g.boundaryNormalDerivativeProjection /\
  g.deltaSlipValueAvailable /\
  g.deltaSlipDotAvailable /\
  g.visibleSlipNonzero /\
  g.kZeroLimitFinite /\
  g.largeKDecayOrBound /\
  g.sourceToValueLinearityCheck /\
  g.normalizationInheritedFromGreenKernel /\
  g.homogeneousModeNotReintroduced /\
  g.grLimitSlipZero /\
  Not g.freeSlipAmplitude /\
  Not g.freeEtaRatio /\
  Not g.manualDeltaSlipTable /\
  Not g.directClPatch /\
  Not g.rawToyLOS /\
  Not g.planckTrialAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem boundary_normal_projection_enables_value_slip_without_planck
    (g : DerivedSlipValueTransportGate)
    (hPolicy : valueTransportReady g -> g.derivedSlipValueTransportGatePassed)
    (h : valueTransportReady g) :
    g.derivedSlipValueTransportGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipValueTransportGate
end JanusFormal

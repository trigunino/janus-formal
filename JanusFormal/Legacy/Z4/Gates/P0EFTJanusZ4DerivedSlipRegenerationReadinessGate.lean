namespace JanusFormal
namespace P0EFTJanusZ4DerivedSlipRegenerationReadinessGate

set_option autoImplicit false

structure DerivedSlipRegenerationReadinessGate where
  slipEquationGatePassed : Prop
  valueSlipTransportClosed : Prop
  boundaryGreenOrNormalModeRequired : Prop
  deltaSlipRegeneratedPerCosmology : Prop
  deltaPhiRegeneratedPerCosmology : Prop
  deltaPsiRegeneratedPerCosmology : Prop
  temperatureSourceRegeneratedWithSlip : Prop
  piSourceRegeneratedWithSlip : Prop
  carrierTangentProjectionRequiredBeforePlanckTrial : Prop
  derivedSlipRegenerationReady : Prop
  planckTrialAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def readinessBlockedUntilValueTransport (g : DerivedSlipRegenerationReadinessGate) : Prop :=
  g.slipEquationGatePassed /\
  Not g.valueSlipTransportClosed /\
  g.boundaryGreenOrNormalModeRequired /\
  Not g.deltaSlipRegeneratedPerCosmology /\
  Not g.deltaPhiRegeneratedPerCosmology /\
  Not g.deltaPsiRegeneratedPerCosmology /\
  Not g.temperatureSourceRegeneratedWithSlip /\
  Not g.piSourceRegeneratedWithSlip /\
  g.carrierTangentProjectionRequiredBeforePlanckTrial /\
  Not g.derivedSlipRegenerationReady /\
  Not g.planckTrialAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem derived_slip_regeneration_remains_blocked_without_value_transport
    (g : DerivedSlipRegenerationReadinessGate)
    (hPolicy : readinessBlockedUntilValueTransport g -> Not g.derivedSlipRegenerationReady)
    (h : readinessBlockedUntilValueTransport g) :
    Not g.derivedSlipRegenerationReady := by
  exact hPolicy h

end P0EFTJanusZ4DerivedSlipRegenerationReadinessGate
end JanusFormal

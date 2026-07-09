import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PolarizationSourceDeltaGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckLensingInputDependenceGate

namespace JanusFormal
namespace P0EFTJanusZ4OfficialPlanckPolarizationSourceDeltaTrial

set_option autoImplicit false

structure OfficialPlanckPolarizationSourceDeltaTrial where
  polarizationSourceGatePassed : Prop
  effectivePolarizationSourceDeltaTrial : Prop
  temperatureChannelFixed : Prop
  lambdaTFixedAtAcousticBest : Prop
  lambdaEScanned : Prop
  eProjectionOnlyTrial : Prop
  theta2QuadrupoleTrial : Prop
  piSourceTrial : Prop
  fullPolarizationSourceTrial : Prop
  theta2PiDerivationSourceTaggedEffective : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  recombinationDeltaEnabled : Prop
  visibilityDeltaEnabled : Prop
  backgroundProjectionChanged : Prop
  primordialDeltaEnabled : Prop
  lensingDeltaEnabled : Prop
  cPhiPhiUnchanged : Prop
  deltaSlipZeroUntilDerived : Prop
  availablePlanckChannelsOnly : Prop
  missingHighlTEEEStandaloneClik : Prop
  lensingShiftClassifiedAsPrimaryCMB : Prop
  officialLikelihoodExecuted : Prop
  fullPlanckVerdict : Prop

def controlledPolarizationTrialReady (t : OfficialPlanckPolarizationSourceDeltaTrial) : Prop :=
  t.polarizationSourceGatePassed /\
  t.effectivePolarizationSourceDeltaTrial /\
  t.temperatureChannelFixed /\
  t.lambdaTFixedAtAcousticBest /\
  t.lambdaEScanned /\
  t.eProjectionOnlyTrial /\
  t.theta2QuadrupoleTrial /\
  t.piSourceTrial /\
  t.fullPolarizationSourceTrial /\
  t.theta2PiDerivationSourceTaggedEffective /\
  Not t.directClPatch /\
  Not t.nativeToyLOSUsed /\
  Not t.recombinationDeltaEnabled /\
  Not t.visibilityDeltaEnabled /\
  Not t.backgroundProjectionChanged /\
  Not t.primordialDeltaEnabled /\
  Not t.lensingDeltaEnabled /\
  t.cPhiPhiUnchanged /\
  t.deltaSlipZeroUntilDerived /\
  t.availablePlanckChannelsOnly /\
  t.missingHighlTEEEStandaloneClik /\
  t.lensingShiftClassifiedAsPrimaryCMB

theorem ready_trial_can_execute_likelihood
    (t : OfficialPlanckPolarizationSourceDeltaTrial)
    (hPolicy : controlledPolarizationTrialReady t -> t.officialLikelihoodExecuted)
    (h : controlledPolarizationTrialReady t) :
    t.officialLikelihoodExecuted := by
  exact hPolicy h

theorem controlled_trial_is_not_full_planck_verdict
    (t : OfficialPlanckPolarizationSourceDeltaTrial)
    (hPolicy : t.officialLikelihoodExecuted -> Not t.fullPlanckVerdict)
    (h : t.officialLikelihoodExecuted) :
    Not t.fullPlanckVerdict := by
  exact hPolicy h

end P0EFTJanusZ4OfficialPlanckPolarizationSourceDeltaTrial
end JanusFormal

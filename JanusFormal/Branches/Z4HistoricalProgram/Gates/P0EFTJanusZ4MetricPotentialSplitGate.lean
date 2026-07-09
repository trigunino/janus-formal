import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4WeylLateISWConsistencyGate

namespace JanusFormal
namespace P0EFTJanusZ4MetricPotentialSplitGate

set_option autoImplicit false

structure MetricPotentialSplitGate where
  sharedWeylDeltaPreserved : Prop
  deltaPhiPlusDeltaPsiEqualsXZ4 : Prop
  deltaPhiMinusDeltaPsiEqualsDeltaSlipZ4 : Prop
  slipDeltaExplicitlyTagged : Prop
  arbitraryPhiPsiSplit : Prop
  independentPhiSource : Prop
  independentPsiSource : Prop
  etaRatioUsedAsPrimary : Prop
  etaDiagnosticGuarded : Prop
  muSigmaDiagnosticGuarded : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  recombinationDeltaEnabled : Prop
  visibilityDeltaEnabled : Prop
  acousticDeltaEnabled : Prop
  polarizationDeltaEnabled : Prop
  primordialDeltaEnabled : Prop
  metricPotentialSplitGatePassed : Prop
  earlyAcousticDrivingGateAllowed : Prop
  officialPlanckTrialAllowed : Prop

def metricPotentialSplitReady (g : MetricPotentialSplitGate) : Prop :=
  g.sharedWeylDeltaPreserved /\
  g.deltaPhiPlusDeltaPsiEqualsXZ4 /\
  g.deltaPhiMinusDeltaPsiEqualsDeltaSlipZ4 /\
  g.slipDeltaExplicitlyTagged /\
  Not g.arbitraryPhiPsiSplit /\
  Not g.independentPhiSource /\
  Not g.independentPsiSource /\
  Not g.etaRatioUsedAsPrimary /\
  g.etaDiagnosticGuarded /\
  g.muSigmaDiagnosticGuarded /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.recombinationDeltaEnabled /\
  Not g.visibilityDeltaEnabled /\
  Not g.acousticDeltaEnabled /\
  Not g.polarizationDeltaEnabled /\
  Not g.primordialDeltaEnabled

theorem split_ready_implies_metric_gate
    (g : MetricPotentialSplitGate)
    (hPolicy : metricPotentialSplitReady g -> g.metricPotentialSplitGatePassed)
    (h : metricPotentialSplitReady g) :
    g.metricPotentialSplitGatePassed := by
  exact hPolicy h

theorem metric_gate_allows_acoustic_gate_not_planck
    (g : MetricPotentialSplitGate)
    (hAcoustic : g.metricPotentialSplitGatePassed -> g.earlyAcousticDrivingGateAllowed)
    (hNoPlanck : g.metricPotentialSplitGatePassed -> Not g.officialPlanckTrialAllowed)
    (h : g.metricPotentialSplitGatePassed) :
    g.earlyAcousticDrivingGateAllowed /\ Not g.officialPlanckTrialAllowed := by
  exact And.intro (hAcoustic h) (hNoPlanck h)

end P0EFTJanusZ4MetricPotentialSplitGate
end JanusFormal

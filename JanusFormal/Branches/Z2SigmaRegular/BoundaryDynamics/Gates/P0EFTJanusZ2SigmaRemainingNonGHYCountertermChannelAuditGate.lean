import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaRemainingNonGHYCountertermChannelAuditGate

set_option autoImplicit false

structure RemainingNonGHYCountertermChannelAuditGate where
  linearKGHYChannelRemoved : Prop
  torsionPullbackChannelZero : Prop
  immirziRadialContractionZero : Prop
  metricNonGHYTraceClosedOrAbsent : Prop
  extrinsicNonGHYTraceClosedOrAbsent : Prop
  fullImmirziNonradialClosedOrAbsent : Prop
  localProjectedSpinorResidualChannelClosedOrAbsent : Prop
  connectionResidualChannelClosedOrAbsent : Prop
  embeddingResidualChannelClosedOrAbsent : Prop
  matterFluxResidualChannelClosedOrAbsent : Prop
  remainingNonGHYChannelAbsenceProved : Prop
  eCountertermZeroConditionallyAllowed : Prop
  missingChannelsTreatedAsZero : Prop

def knownZeroChannelsClosed
    (g : RemainingNonGHYCountertermChannelAuditGate) : Prop :=
  g.linearKGHYChannelRemoved /\
  g.torsionPullbackChannelZero /\
  g.immirziRadialContractionZero

def allRemainingNonGHYChannelsClosedOrAbsent
    (g : RemainingNonGHYCountertermChannelAuditGate) : Prop :=
  g.metricNonGHYTraceClosedOrAbsent /\
  g.extrinsicNonGHYTraceClosedOrAbsent /\
  g.fullImmirziNonradialClosedOrAbsent /\
  g.localProjectedSpinorResidualChannelClosedOrAbsent /\
  g.connectionResidualChannelClosedOrAbsent /\
  g.embeddingResidualChannelClosedOrAbsent /\
  g.matterFluxResidualChannelClosedOrAbsent

theorem counterterm_zero_requires_absence_of_remaining_channels
    (g : RemainingNonGHYCountertermChannelAuditGate)
    (_hZero : knownZeroChannelsClosed g)
    (hAllowed : g.eCountertermZeroConditionallyAllowed)
    (hImplies : g.eCountertermZeroConditionallyAllowed ->
      g.remainingNonGHYChannelAbsenceProved) :
    g.remainingNonGHYChannelAbsenceProved := by
  exact hImplies hAllowed

end P0EFTJanusZ2SigmaRemainingNonGHYCountertermChannelAuditGate
end JanusFormal

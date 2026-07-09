import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4Theta2TightCouplingClosureGate

namespace JanusFormal
namespace P0EFTJanusZ4TEEETransportSmoothnessGate

set_option autoImplicit false

structure TEEETransportSmoothnessGate where
  theta2TightCouplingDerivedEffective : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  visibilityDeltaEnabled : Prop
  recombinationDeltaEnabled : Prop
  backgroundProjectionChanged : Prop
  soundHorizonChanged : Prop
  dragRulerChanged : Prop
  primordialDeltaEnabled : Prop
  lensingCPhiPhiFrozen : Prop
  slipFrozen : Prop
  comparedAgainstSourceTaggedTheta2 : Prop
  teSmoothnessImproved : Prop
  eeSmoothnessImproved : Prop
  gatePassed : Prop
  jointGateRerunRecommended : Prop
  fullPlanckVerdict : Prop

def transportSmoothnessReady (g : TEEETransportSmoothnessGate) : Prop :=
  g.theta2TightCouplingDerivedEffective /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed /\
  Not g.visibilityDeltaEnabled /\
  Not g.recombinationDeltaEnabled /\
  Not g.backgroundProjectionChanged /\
  Not g.soundHorizonChanged /\
  Not g.dragRulerChanged /\
  Not g.primordialDeltaEnabled /\
  g.lensingCPhiPhiFrozen /\
  g.slipFrozen /\
  g.comparedAgainstSourceTaggedTheta2 /\
  g.teSmoothnessImproved /\
  g.eeSmoothnessImproved

theorem ready_implies_transport_gate
    (g : TEEETransportSmoothnessGate)
    (hPolicy : transportSmoothnessReady g -> g.gatePassed)
    (h : transportSmoothnessReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem transport_gate_recommends_joint_rerun
    (g : TEEETransportSmoothnessGate)
    (hPolicy : g.gatePassed -> g.jointGateRerunRecommended /\ Not g.fullPlanckVerdict)
    (h : g.gatePassed) :
    g.jointGateRerunRecommended /\ Not g.fullPlanckVerdict := by
  exact hPolicy h

end P0EFTJanusZ4TEEETransportSmoothnessGate
end JanusFormal

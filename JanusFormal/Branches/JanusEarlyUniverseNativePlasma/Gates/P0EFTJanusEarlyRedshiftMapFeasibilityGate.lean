namespace JanusFormal
namespace P0EFTJanusEarlyRedshiftMapFeasibilityGate

set_option autoImplicit false

structure EarlyRedshiftMapFeasibilityGate where
  throatLowerBoundImported : Prop
  targetRedshiftDeclared : Prop
  requiredExponentComputed : Prop
  paperNativeGeometricMapFails : Prop
  eq40ClockMapFails : Prop
  a3OccupationMapFailsTarget : Prop
  fourPowerMapReachesButSpeculative : Prop
  earlyPhotonTransportLawRequired : Prop
  lateM18RedshiftKeptSeparate : Prop

def earlyRedshiftFeasibilityReady
    (g : EarlyRedshiftMapFeasibilityGate) : Prop :=
  g.throatLowerBoundImported /\
  g.targetRedshiftDeclared /\
  g.requiredExponentComputed /\
  g.paperNativeGeometricMapFails /\
  g.eq40ClockMapFails /\
  g.a3OccupationMapFailsTarget /\
  g.fourPowerMapReachesButSpeculative /\
  g.earlyPhotonTransportLawRequired /\
  g.lateM18RedshiftKeptSeparate

theorem early_redshift_requires_transport_not_guess
    (g : EarlyRedshiftMapFeasibilityGate)
    (hReady : earlyRedshiftFeasibilityReady g) :
    g.earlyPhotonTransportLawRequired /\ g.fourPowerMapReachesButSpeculative := by
  exact And.intro hReady.2.2.2.2.2.2.2.1 hReady.2.2.2.2.2.2.1

end P0EFTJanusEarlyRedshiftMapFeasibilityGate
end JanusFormal

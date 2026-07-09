namespace JanusFormal
namespace P0EFTTorsionVectorNeffPlanckGate

set_option autoImplicit false

structure TorsionVectorNeffPlanckGate where
  requiredNeffComputed : Prop
  fullPlanckGateRun : Prop
  improvesPlanck : Prop
  acceptedByPlanck : Prop
  torsionVectorGeometryDerived : Prop

def routeADiagnosticReady (g : TorsionVectorNeffPlanckGate) : Prop :=
  g.requiredNeffComputed /\ g.fullPlanckGateRun

def routeANoFitReady (g : TorsionVectorNeffPlanckGate) : Prop :=
  routeADiagnosticReady g /\
  g.improvesPlanck /\
  g.acceptedByPlanck /\
  g.torsionVectorGeometryDerived

theorem route_a_diagnostic_ready_from_neff_and_planck
    (g : TorsionVectorNeffPlanckGate)
    (hN : g.requiredNeffComputed)
    (hP : g.fullPlanckGateRun) :
    routeADiagnosticReady g := by
  exact And.intro hN hP

theorem rejected_planck_blocks_route_a_no_fit
    (g : TorsionVectorNeffPlanckGate)
    (hReject : Not g.acceptedByPlanck) :
    Not (routeANoFitReady g) := by
  intro h
  exact hReject h.right.right.left

end P0EFTTorsionVectorNeffPlanckGate
end JanusFormal

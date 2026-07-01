namespace JanusFormal
namespace P0EFTImmirziGeffPlanckGate

set_option autoImplicit false

structure ImmirziGeffPlanckGate where
  geffBoostTrialRun : Prop
  naiveBackgroundOnlyRejected : Prop
  perturbationSectorConsistent : Prop
  planckAccepted : Prop

def routeBDiagnosticReady (g : ImmirziGeffPlanckGate) : Prop :=
  g.geffBoostTrialRun /\ g.naiveBackgroundOnlyRejected

def routeBNoFitReady (g : ImmirziGeffPlanckGate) : Prop :=
  routeBDiagnosticReady g /\
  g.perturbationSectorConsistent /\
  g.planckAccepted

theorem naive_geff_rejection_closes_background_only_route
    (g : ImmirziGeffPlanckGate)
    (hRun : g.geffBoostTrialRun)
    (hRejected : g.naiveBackgroundOnlyRejected) :
    routeBDiagnosticReady g := by
  exact And.intro hRun hRejected

theorem missing_perturbation_sector_blocks_route_b
    (g : ImmirziGeffPlanckGate)
    (hMissing : Not g.perturbationSectorConsistent) :
    Not (routeBNoFitReady g) := by
  intro h
  exact hMissing h.right.left

end P0EFTImmirziGeffPlanckGate
end JanusFormal

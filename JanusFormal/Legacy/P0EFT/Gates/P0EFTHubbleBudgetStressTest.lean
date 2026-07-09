namespace JanusFormal
namespace P0EFTHubbleBudgetStressTest

set_option autoImplicit false

structure HubbleBudgetStressTest where
  baselineScored : Prop
  spinTermRemovedScored : Prop
  torsionProfileFrozenScored : Prop
  omegaMScanScored : Prop
  radialDHFailureDominant : Prop
  culpritTermIsolated : Prop

def stressTestReady (s : HubbleBudgetStressTest) : Prop :=
  s.baselineScored /\
  s.spinTermRemovedScored /\
  s.torsionProfileFrozenScored /\
  s.omegaMScanScored

def culpritIsolationReady (s : HubbleBudgetStressTest) : Prop :=
  stressTestReady s /\
  s.radialDHFailureDominant /\
  s.culpritTermIsolated

theorem scored_variants_close_stress_test_gate
    (s : HubbleBudgetStressTest)
    (hBase : s.baselineScored)
    (hSpin : s.spinTermRemovedScored)
    (hTorsion : s.torsionProfileFrozenScored)
    (hOmegaM : s.omegaMScanScored) :
    stressTestReady s := by
  exact And.intro hBase (And.intro hSpin (And.intro hTorsion hOmegaM))

theorem missing_culprit_keeps_budget_open
    (s : HubbleBudgetStressTest)
    (hMissing : Not s.culpritTermIsolated) :
    Not (culpritIsolationReady s) := by
  intro h
  exact hMissing h.right.right

end P0EFTHubbleBudgetStressTest
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2ObservationalAlphaSectorPolicyGate

set_option autoImplicit false

structure ObservationalAlphaSectorPolicyGate where
  supernovaAvailable : Prop
  baoAvailable : Prop
  hzAvailable : Prop
  noFitPrediction : Prop

def alphaSectorObservable (g : ObservationalAlphaSectorPolicyGate) : Prop :=
  g.supernovaAvailable \/ g.baoAvailable

def absoluteScaleBreakingPossible (g : ObservationalAlphaSectorPolicyGate) : Prop :=
  g.baoAvailable

def observationalSectorSelectionReady (g : ObservationalAlphaSectorPolicyGate) : Prop :=
  alphaSectorObservable g /\ absoluteScaleBreakingPossible g

def noFitAlphaDerived (g : ObservationalAlphaSectorPolicyGate) : Prop :=
  g.noFitPrediction

theorem observational_selection_does_not_imply_no_fit
    (g : ObservationalAlphaSectorPolicyGate)
    (_h : observationalSectorSelectionReady g)
    (hNoFit : Not g.noFitPrediction) :
    Not (noFitAlphaDerived g) := by
  intro h
  exact hNoFit h

theorem supernova_only_does_not_break_absolute_scale
    (g : ObservationalAlphaSectorPolicyGate)
    (_hSN : g.supernovaAvailable)
    (hNoBAO : Not g.baoAvailable) :
    Not (absoluteScaleBreakingPossible g) := by
  intro h
  exact hNoBAO h

end P0EFTJanusZ2ObservationalAlphaSectorPolicyGate
end JanusFormal

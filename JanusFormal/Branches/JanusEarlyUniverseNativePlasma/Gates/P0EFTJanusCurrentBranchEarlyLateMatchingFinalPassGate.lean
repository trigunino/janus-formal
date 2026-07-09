import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusTwoCoshBranchMatchingObstructionGate

namespace JanusFormal
namespace P0EFTJanusCurrentBranchEarlyLateMatchingFinalPassGate

set_option autoImplicit false

structure CurrentBranchEarlyLateMatchingFinalPassGate where
  EntropyCutoffSuppliesAmin : Prop
  SameLateCoshBranchCompatible : Prop
  TwoCoshC1MatchingClosed : Prop
  NativeEarlyHJDerived : Prop
  TransitionLawDerived : Prop

def CurrentBranchMatchingClosed
    (g : CurrentBranchEarlyLateMatchingFinalPassGate) : Prop :=
  g.EntropyCutoffSuppliesAmin /\
  g.SameLateCoshBranchCompatible /\
  g.TwoCoshC1MatchingClosed /\
  g.NativeEarlyHJDerived /\
  g.TransitionLawDerived

def CurrentBranchMatchingFrontier
    (g : CurrentBranchEarlyLateMatchingFinalPassGate) : Prop :=
  g.EntropyCutoffSuppliesAmin /\
  Not g.SameLateCoshBranchCompatible /\
  Not g.TwoCoshC1MatchingClosed /\
  Not g.NativeEarlyHJDerived /\
  Not g.TransitionLawDerived

theorem current_entropy_throat_branch_matching_not_closed
    (g : CurrentBranchEarlyLateMatchingFinalPassGate)
    (hFrontier : CurrentBranchMatchingFrontier g) :
    Not (CurrentBranchMatchingClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusCurrentBranchEarlyLateMatchingFinalPassGate
end JanusFormal

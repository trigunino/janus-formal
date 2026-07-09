import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusEntropyCutoffExactShapeCompatibilityGate

namespace JanusFormal
namespace P0EFTJanusTwoCoshBranchMatchingObstructionGate

set_option autoImplicit false

structure TwoCoshBranchMatchingObstructionGate where
  C0ScaleFactorMatchPossible : Prop
  LateThroatShapeVelocityZero : Prop
  EarlyBranchShapeVelocityNonzeroAtLateThroatScale : Prop
  C1MatchWithoutTransitionSurface : Prop
  TransitionLawDerived : Prop

def TwoCoshBranchMatchClosed
    (g : TwoCoshBranchMatchingObstructionGate) : Prop :=
  g.C0ScaleFactorMatchPossible /\
  g.C1MatchWithoutTransitionSurface

def TwoCoshBranchMatchFrontier
    (g : TwoCoshBranchMatchingObstructionGate) : Prop :=
  g.C0ScaleFactorMatchPossible /\
  g.LateThroatShapeVelocityZero /\
  g.EarlyBranchShapeVelocityNonzeroAtLateThroatScale /\
  Not g.C1MatchWithoutTransitionSurface /\
  Not g.TransitionLawDerived

theorem two_cosh_throat_gluing_needs_transition_law
    (g : TwoCoshBranchMatchingObstructionGate)
    (hFrontier : TwoCoshBranchMatchFrontier g) :
    Not (TwoCoshBranchMatchClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2

end P0EFTJanusTwoCoshBranchMatchingObstructionGate
end JanusFormal

import JanusFormal.P0EFTJanusComplexRealityCP1FromJanusPTGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityAroundSigmaCP1HolonomyActionGate

set_option autoImplicit false

structure AroundSigmaCP1HolonomyActionGate where
  aroundSigmaZ2CycleAvailable : Prop
  cp1MathematicalCandidateReady : Prop
  cp1DerivedFromJanusPT : Prop
  spinLiftOfAroundSigmaSpecified : Prop
  noncentralProjectiveActionDerived : Prop
  actionPreservesCP1KKSForm : Prop

def holonomyActionSymbolicallyClassified
    (g : AroundSigmaCP1HolonomyActionGate) : Prop :=
  g.aroundSigmaZ2CycleAvailable /\
  g.cp1MathematicalCandidateReady

def aroundSigmaActionOnCP1Derived
    (g : AroundSigmaCP1HolonomyActionGate) : Prop :=
  holonomyActionSymbolicallyClassified g /\
  g.cp1DerivedFromJanusPT /\
  g.spinLiftOfAroundSigmaSpecified /\
  g.noncentralProjectiveActionDerived /\
  g.actionPreservesCP1KKSForm

theorem central_lift_not_enough_without_noncentral_action
    (g : AroundSigmaCP1HolonomyActionGate)
    (hMissing : Not g.noncentralProjectiveActionDerived) :
    Not (aroundSigmaActionOnCP1Derived g) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTJanusComplexRealityAroundSigmaCP1HolonomyActionGate
end JanusFormal

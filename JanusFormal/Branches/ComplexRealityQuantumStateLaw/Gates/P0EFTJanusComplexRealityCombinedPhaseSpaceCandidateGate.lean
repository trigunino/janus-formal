import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealityQuantumCandidateWorkbenchGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityCombinedPhaseSpaceCandidateGate

set_option autoImplicit false

structure CombinedPhaseSpaceCandidateGate where
  individualCandidatesPreserved : Prop
  baseSupportAvailable : Prop
  cp1FiberConstructedMathematically : Prop
  aroundSigmaCycleAvailable : Prop
  cp1DerivedFromJanusPT : Prop
  aroundSigmaActionOnCP1Derived : Prop
  combinedKKSPeriodNonzero : Prop
  sectorSelectionLawDerived : Prop
  alphaMapDerived : Prop
  alphaGenerated : Prop

def combinedCandidateCoherent (g : CombinedPhaseSpaceCandidateGate) : Prop :=
  g.individualCandidatesPreserved /\
  g.baseSupportAvailable /\
  g.cp1FiberConstructedMathematically /\
  g.aroundSigmaCycleAvailable

def combinedCandidatePhysicallyClosed
    (g : CombinedPhaseSpaceCandidateGate) : Prop :=
  combinedCandidateCoherent g /\
  g.cp1DerivedFromJanusPT /\
  g.aroundSigmaActionOnCP1Derived /\
  g.combinedKKSPeriodNonzero /\
  g.sectorSelectionLawDerived /\
  g.alphaMapDerived

def alphaGeneratedByCombinedCandidate
    (g : CombinedPhaseSpaceCandidateGate) : Prop :=
  combinedCandidatePhysicallyClosed g /\ g.alphaGenerated

theorem coherent_combination_without_holonomy_action_not_closed
    (g : CombinedPhaseSpaceCandidateGate)
    (hMissing : Not g.aroundSigmaActionOnCP1Derived) :
    Not (combinedCandidatePhysicallyClosed g) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTJanusComplexRealityCombinedPhaseSpaceCandidateGate
end JanusFormal

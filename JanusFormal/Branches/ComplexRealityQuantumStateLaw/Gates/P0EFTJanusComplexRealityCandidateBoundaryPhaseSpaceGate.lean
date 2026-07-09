namespace JanusFormal
namespace P0EFTJanusComplexRealityCandidateBoundaryPhaseSpaceGate

set_option autoImplicit false

structure CandidateBoundaryPhaseSpaceGate where
  compactBoundaryPhaseSpaceConstructed : Prop
  closedTwoCycleConstructed : Prop
  kksFormDeclared : Prop
  symbolicPeriodNonzeroIfJNonzero : Prop
  prequantizationConditionDeclared : Prop
  sourceDerivedFromJanusPT : Prop
  mapFromSpinOrbitJToAlphaDerived : Prop
  primitiveNonzeroSectorSelected : Prop
  alphaGenerated : Prop

def candidateConstructed (g : CandidateBoundaryPhaseSpaceGate) : Prop :=
  g.compactBoundaryPhaseSpaceConstructed /\
  g.closedTwoCycleConstructed /\
  g.kksFormDeclared /\
  g.symbolicPeriodNonzeroIfJNonzero /\
  g.prequantizationConditionDeclared

def candidatePhysicallyAccepted (g : CandidateBoundaryPhaseSpaceGate) : Prop :=
  candidateConstructed g /\
  g.sourceDerivedFromJanusPT /\
  g.mapFromSpinOrbitJToAlphaDerived /\
  g.primitiveNonzeroSectorSelected

def alphaGeneratedByCandidate (g : CandidateBoundaryPhaseSpaceGate) : Prop :=
  candidatePhysicallyAccepted g /\ g.alphaGenerated

theorem constructed_candidate_without_alpha_map_does_not_generate_alpha
    (g : CandidateBoundaryPhaseSpaceGate)
    (hMissing : Not g.mapFromSpinOrbitJToAlphaDerived) :
    Not (candidatePhysicallyAccepted g) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTJanusComplexRealityCandidateBoundaryPhaseSpaceGate
end JanusFormal

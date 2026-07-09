import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealityAroundSigmaCP1HolonomyActionGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityCombinedKKSPeriodGate

set_option autoImplicit false

structure CombinedKKSPeriodGate where
  cp1KKSPeriodSymbolic : Prop
  periodFormulaNonzeroIfJNonzero : Prop
  cp1DerivedFromJanusPT : Prop
  aroundSigmaActionOnCP1Derived : Prop
  sectorSelectionLawDerived : Prop
  jNonzeroSelected : Prop
  alphaGenerated : Prop

def symbolicCombinedKKSPeriodNonzero (g : CombinedKKSPeriodGate) : Prop :=
  g.cp1KKSPeriodSymbolic /\ g.periodFormulaNonzeroIfJNonzero

def janusDerivedCombinedKKSPeriodNonzero (g : CombinedKKSPeriodGate) : Prop :=
  symbolicCombinedKKSPeriodNonzero g /\
  g.cp1DerivedFromJanusPT /\
  g.aroundSigmaActionOnCP1Derived /\
  g.sectorSelectionLawDerived /\
  g.jNonzeroSelected

def alphaGeneratedByCombinedPeriod (g : CombinedKKSPeriodGate) : Prop :=
  janusDerivedCombinedKKSPeriodNonzero g /\ g.alphaGenerated

theorem symbolic_period_without_sector_selection_does_not_generate_alpha
    (g : CombinedKKSPeriodGate)
    (hMissing : Not g.sectorSelectionLawDerived) :
    Not (alphaGeneratedByCombinedPeriod g) := by
  intro h
  exact hMissing h.left.right.right.right.left

end P0EFTJanusComplexRealityCombinedKKSPeriodGate
end JanusFormal

import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstClassicalLimitGate

namespace JanusFormal
namespace P0EFTJanusQuantumFirstVerdictGate

set_option autoImplicit false

structure QuantumFirstVerdictGate where
  conditionalAlphaSpectrumReady : Prop
  conditionalClassicalLimitReady : Prop
  boundaryMassOperatorDerived : Prop
  primitiveSectorLawDerived : Prop
  noFitAlphaGenerated : Prop

def quantumFirstConditionalProgress (g : QuantumFirstVerdictGate) : Prop :=
  g.conditionalAlphaSpectrumReady /\ g.conditionalClassicalLimitReady

def quantumFirstNoFitClosed (g : QuantumFirstVerdictGate) : Prop :=
  quantumFirstConditionalProgress g /\
  g.boundaryMassOperatorDerived /\
  g.primitiveSectorLawDerived /\
  g.noFitAlphaGenerated

theorem conditional_progress_without_mass_law_is_not_no_fit
    (g : QuantumFirstVerdictGate)
    (hMissingMass : Not g.boundaryMassOperatorDerived) :
    Not (quantumFirstNoFitClosed g) := by
  intro h
  exact hMissingMass h.right.left

end P0EFTJanusQuantumFirstVerdictGate
end JanusFormal

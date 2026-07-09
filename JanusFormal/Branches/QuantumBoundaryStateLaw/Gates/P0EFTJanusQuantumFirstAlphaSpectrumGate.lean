import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstCP1TQFTPhaseSpaceGate

namespace JanusFormal
namespace P0EFTJanusQuantumFirstAlphaSpectrumGate

set_option autoImplicit false

structure QuantumFirstAlphaSpectrumGate where
  quantumLabelsAvailable : Prop
  boundaryMassOperatorDerived : Prop
  alphaMassMapDeclared : Prop
  alphaSpectrumConditional : Prop
  alphaSpectrumNumerical : Prop

def conditionalAlphaSpectrumReady (g : QuantumFirstAlphaSpectrumGate) : Prop :=
  g.quantumLabelsAvailable /\ g.alphaMassMapDeclared /\ g.alphaSpectrumConditional

def predictiveAlphaSpectrumReady (g : QuantumFirstAlphaSpectrumGate) : Prop :=
  conditionalAlphaSpectrumReady g /\ g.boundaryMassOperatorDerived /\ g.alphaSpectrumNumerical

theorem no_mass_operator_blocks_predictive_alpha
    (g : QuantumFirstAlphaSpectrumGate)
    (hMissing : Not g.boundaryMassOperatorDerived) :
    Not (predictiveAlphaSpectrumReady g) := by
  intro h
  exact hMissing h.right.left

end P0EFTJanusQuantumFirstAlphaSpectrumGate
end JanusFormal

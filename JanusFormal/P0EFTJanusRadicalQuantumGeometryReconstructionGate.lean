namespace JanusFormal
namespace P0EFTJanusRadicalQuantumGeometryReconstructionGate

set_option autoImplicit false

structure RadicalQuantumGeometryGate where
  classicalSigmaNotPrimary : Prop
  quantumStateSpacePrimary : Prop
  emergentTopologyMapDeclared : Prop
  emergentMetricMapDeclared : Prop
  boundaryMassOperatorDerived : Prop
  alphaGeneratedNoFit : Prop

def radicalBranchOpened (g : RadicalQuantumGeometryGate) : Prop :=
  g.classicalSigmaNotPrimary /\
  g.quantumStateSpacePrimary /\
  g.emergentTopologyMapDeclared /\
  g.emergentMetricMapDeclared /\
  Not g.boundaryMassOperatorDerived /\
  Not g.alphaGeneratedNoFit

theorem radical_quantum_geometry_still_requires_mass_operator
    (g : RadicalQuantumGeometryGate)
    (h : radicalBranchOpened g) :
    Not g.boundaryMassOperatorDerived := by
  exact h.right.right.right.right.left

theorem radical_quantum_geometry_not_yet_no_fit
    (g : RadicalQuantumGeometryGate)
    (h : radicalBranchOpened g) :
    Not g.alphaGeneratedNoFit := by
  exact h.right.right.right.right.right

end P0EFTJanusRadicalQuantumGeometryReconstructionGate
end JanusFormal

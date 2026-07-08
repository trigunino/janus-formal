namespace JanusFormal
namespace P0EFTJanusChiLLSelectionRepriseGate

set_option autoImplicit false

structure ChiLLSelectionRepriseGate where
  llbraneMassRelationAlreadyDerived : Prop
  discreteSectorFamilyAlreadyBuilt : Prop
  primitiveFluxNoGoAlreadyRecorded : Prop
  chiLLSelectedNoFit : Prop
  remainingBlockerIsSelectionLaw : Prop

def repriseStatus (g : ChiLLSelectionRepriseGate) : Prop :=
  g.llbraneMassRelationAlreadyDerived /\
  g.discreteSectorFamilyAlreadyBuilt /\
  g.primitiveFluxNoGoAlreadyRecorded /\
  Not g.chiLLSelectedNoFit /\
  g.remainingBlockerIsSelectionLaw

theorem chi_ll_reprise_still_needs_selection_law
    (g : ChiLLSelectionRepriseGate)
    (h : repriseStatus g) :
    Not g.chiLLSelectedNoFit := by
  exact h.right.right.right.left

end P0EFTJanusChiLLSelectionRepriseGate
end JanusFormal

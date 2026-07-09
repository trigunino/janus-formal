namespace JanusFormal
namespace P0EFTJanusAminSelectionCandidateMatrixGate

set_option autoImplicit false

structure AminSelectionCandidateMatrixGate where
  requiredAminDeclared : Prop
  dragReachDefinitionRejectedAsCircular : Prop
  eq40LengthRatioUnderdetermined : Prop
  sahaSelectsDragNotThroat : Prop
  quantumCutoffNeedsNewInput : Prop
  topologicalIntegerOpenOnlyIfNDerived : Prop
  lateSNThroatFailsPredrag : Prop
  noCurrentNoFitSelectorClosed : Prop

def aminSelectionMatrixReady
    (g : AminSelectionCandidateMatrixGate) : Prop :=
  g.requiredAminDeclared /\
  g.dragReachDefinitionRejectedAsCircular /\
  g.eq40LengthRatioUnderdetermined /\
  g.sahaSelectsDragNotThroat /\
  g.quantumCutoffNeedsNewInput /\
  g.topologicalIntegerOpenOnlyIfNDerived /\
  g.lateSNThroatFailsPredrag /\
  g.noCurrentNoFitSelectorClosed

theorem amin_selector_still_open
    (g : AminSelectionCandidateMatrixGate)
    (hReady : aminSelectionMatrixReady g) :
    g.noCurrentNoFitSelectorClosed /\ g.topologicalIntegerOpenOnlyIfNDerived := by
  exact And.intro hReady.2.2.2.2.2.2.2 hReady.2.2.2.2.2.1

end P0EFTJanusAminSelectionCandidateMatrixGate
end JanusFormal

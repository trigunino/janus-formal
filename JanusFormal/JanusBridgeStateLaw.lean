import JanusFormal.P0EFTJanusBridgeStateLawOpeningGate
import JanusFormal.P0EFTJanusBridgeStateLawCandidateDiscriminatorGate
import JanusFormal.P0EFTJanusBridgeStateLawCrediblePistesTerminalGate
import JanusFormal.P0EFTJanusAlphaSuperselectionSectorProgramGate
import JanusFormal.P0EFTJanusAlphaSuperselectionObservationEndpointGate

namespace JanusFormal
namespace JanusBridgeStateLaw

set_option autoImplicit false

structure BranchStatus where
  bridgeStateLawOpened : Prop
  chiLLSelectedNoFit : Prop
  observationSelectionOnly : Prop

def openedButNotPredictiveYet (s : BranchStatus) : Prop :=
  s.bridgeStateLawOpened /\ Not s.chiLLSelectedNoFit /\ Not s.observationSelectionOnly

theorem bridge_state_law_requires_internal_selector
    (s : BranchStatus)
    (h : openedButNotPredictiveYet s) :
    Not s.chiLLSelectedNoFit := by
  exact h.right.left

end JanusBridgeStateLaw
end JanusFormal

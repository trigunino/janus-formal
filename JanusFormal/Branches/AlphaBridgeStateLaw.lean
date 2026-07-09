/- Branch head: bridge state law / alpha superselection. -/

import JanusFormal.Branches.AlphaBridgeStateLaw.Gates.P0EFTJanusAlphaBridgeStateLawOpeningGate
import JanusFormal.Branches.AlphaBridgeStateLaw.Gates.P0EFTJanusAlphaBridgeStateLawCandidateDiscriminatorGate
import JanusFormal.Branches.AlphaBridgeStateLaw.Gates.P0EFTJanusAlphaBridgeStateLawCrediblePistesTerminalGate
import JanusFormal.Branches.AlphaBridgeStateLaw.Gates.P0EFTJanusAlphaSuperselectionSectorProgramGate
import JanusFormal.Branches.AlphaBridgeStateLaw.Gates.P0EFTJanusAlphaSuperselectionObservationEndpointGate
import JanusFormal.Branches.AlphaBridgeStateLaw.Gates.P0EFTJanusAlphaSuperselectionObservationClosureGate

namespace JanusFormal
namespace Branches
namespace AlphaBridgeStateLaw

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

end AlphaBridgeStateLaw
end Branches
end JanusFormal

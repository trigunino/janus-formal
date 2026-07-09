/- Branch head: bridge state law / alpha superselection. -/

import JanusFormal.Branches.BridgeStateLaw.Gates.P0EFTJanusBridgeStateLawOpeningGate
import JanusFormal.Branches.BridgeStateLaw.Gates.P0EFTJanusBridgeStateLawCandidateDiscriminatorGate
import JanusFormal.Branches.BridgeStateLaw.Gates.P0EFTJanusBridgeStateLawCrediblePistesTerminalGate
import JanusFormal.Branches.BridgeStateLaw.Gates.P0EFTJanusAlphaSuperselectionSectorProgramGate
import JanusFormal.Branches.BridgeStateLaw.Gates.P0EFTJanusAlphaSuperselectionObservationEndpointGate
import JanusFormal.Branches.BridgeStateLaw.Gates.P0EFTJanusAlphaSuperselectionObservationClosureGate
import JanusFormal.Branches.BridgeStateLaw.Gates.P0EFTJanusNativeBAORulerContractGate

namespace JanusFormal
namespace Branches
namespace BridgeStateLaw

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

end BridgeStateLaw
end Branches
end JanusFormal

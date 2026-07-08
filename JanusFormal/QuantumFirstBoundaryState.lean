import JanusFormal.P0EFTJanusQuantumFirstBoundaryStateOpeningGate
import JanusFormal.P0EFTJanusQuantumFirstCP1TQFTPhaseSpaceGate
import JanusFormal.P0EFTJanusQuantumFirstAlphaSpectrumGate
import JanusFormal.P0EFTJanusQuantumFirstClassicalLimitGate
import JanusFormal.P0EFTJanusQuantumFirstVerdictGate
import JanusFormal.P0EFTJanusQuantumFirstBoundaryMassOperatorNoGoGate
import JanusFormal.P0EFTJanusQuantumFirstExhaustionVerdictGate

namespace JanusFormal
namespace QuantumFirstBoundaryState

set_option autoImplicit false

structure BranchStatus where
  quantumFirstProgramOpen : Prop
  conditionalAlphaSpectrumReady : Prop
  conditionalClassicalLimitReady : Prop
  boundaryMassOperatorRoutesExhausted : Prop
  noFitAlphaGenerated : Prop

def branchExploredButNotClosed (s : BranchStatus) : Prop :=
  s.quantumFirstProgramOpen /\
  s.conditionalAlphaSpectrumReady /\
  s.conditionalClassicalLimitReady /\
  s.boundaryMassOperatorRoutesExhausted /\
  Not s.noFitAlphaGenerated

theorem explored_branch_still_requires_alpha_law
    (s : BranchStatus)
    (h : branchExploredButNotClosed s) :
    Not s.noFitAlphaGenerated := by
  exact h.right.right.right.right

end QuantumFirstBoundaryState
end JanusFormal

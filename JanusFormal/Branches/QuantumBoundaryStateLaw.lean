/- Branch head: quantum boundary state / quantum-first alpha program. -/

import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstBoundaryStateOpeningGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstCP1TQFTPhaseSpaceGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstAlphaSpectrumGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstClassicalLimitGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstVerdictGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstBoundaryMassOperatorNoGoGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstExhaustionVerdictGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusRadicalQuantumGeometryReconstructionGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusRadicalQuantumGeometryBottomVerdictGate

namespace JanusFormal
namespace Branches
namespace QuantumBoundaryStateLaw

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

end QuantumBoundaryStateLaw
end Branches
end JanusFormal

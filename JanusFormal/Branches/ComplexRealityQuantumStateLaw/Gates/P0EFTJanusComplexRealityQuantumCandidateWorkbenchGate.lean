import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealityCandidatePhaseSpaceMatrixGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityQuantumCandidateWorkbenchGate

set_option autoImplicit false

structure QuantumCandidateWorkbenchGate where
  sourceMatrixReady : Prop
  activeS2ProjectedToQuantumWorkbench : Prop
  cp1ProjectedToQuantumWorkbench : Prop
  aroundSigmaPhaseProjectedToQuantumWorkbench : Prop
  cp1RankedBestQuantumCandidate : Prop
  anyCandidateAlphaReady : Prop

def workbenchReady (g : QuantumCandidateWorkbenchGate) : Prop :=
  g.sourceMatrixReady /\
  g.activeS2ProjectedToQuantumWorkbench /\
  g.cp1ProjectedToQuantumWorkbench /\
  g.aroundSigmaPhaseProjectedToQuantumWorkbench /\
  g.cp1RankedBestQuantumCandidate /\
  Not g.anyCandidateAlphaReady

theorem quantum_workbench_does_not_fix_alpha
    (g : QuantumCandidateWorkbenchGate)
    (h : workbenchReady g) :
    Not g.anyCandidateAlphaReady := by
  exact h.right.right.right.right.right

end P0EFTJanusComplexRealityQuantumCandidateWorkbenchGate
end JanusFormal

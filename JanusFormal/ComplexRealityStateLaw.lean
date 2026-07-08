import JanusFormal.P0EFTJanusComplexRealitySourceFormulaCurationGate
import JanusFormal.P0EFTJanusComplexRealityEq131KKSProjectionGate
import JanusFormal.P0EFTJanusComplexRealityCoadjointStateSpaceGate
import JanusFormal.P0EFTJanusComplexRealityKKSBoundaryDensityGate
import JanusFormal.P0EFTJanusComplexRealitySigmaBoundaryProjectionGate

namespace JanusFormal
namespace ComplexRealityStateLaw

set_option autoImplicit false

structure BranchStatus where
  sourceFormulaCurationReady : Prop
  eq131KKSProjectionReady : Prop
  coadjointStateSpaceReady : Prop
  globalKKSOrbitNonzero : Prop
  sigmaBoundaryProjectionSymbolicReady : Prop
  sigmaBoundaryProjectionActiveReady : Prop
  kksBoundaryDensityReady : Prop
  alphaGenerated : Prop

def complexRealityBranchFormalized (s : BranchStatus) : Prop :=
  s.sourceFormulaCurationReady /\
  s.eq131KKSProjectionReady /\
  s.coadjointStateSpaceReady /\
  s.globalKKSOrbitNonzero /\
  s.sigmaBoundaryProjectionSymbolicReady /\
  Not s.sigmaBoundaryProjectionActiveReady /\
  Not s.kksBoundaryDensityReady /\
  Not s.alphaGenerated

theorem formalized_branch_still_does_not_predict_alpha
    (s : BranchStatus)
    (h : complexRealityBranchFormalized s) :
    Not s.alphaGenerated := by
  rcases h with ⟨_, _, _, _, _, _, _, hNoAlpha⟩
  exact hNoAlpha

end ComplexRealityStateLaw
end JanusFormal

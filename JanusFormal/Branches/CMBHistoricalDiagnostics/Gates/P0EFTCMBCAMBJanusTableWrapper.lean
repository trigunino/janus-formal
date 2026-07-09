namespace JanusFormal
namespace P0EFTCMBCAMBJanusTableWrapper

set_option autoImplicit false

structure CAMBJanusTableWrapper where
  backendSolverRun : Prop
  janusModifiedGravityTablesConsumed : Prop
  exactCAMBFork : Prop
  boltzmannEquationsModifiedInSolver : Prop
  uncompressedPlanckLikelihoodUsed : Prop

def wrapperReady (w : CAMBJanusTableWrapper) : Prop :=
  w.backendSolverRun /\ w.janusModifiedGravityTablesConsumed

def directCMBLikelihoodReady (w : CAMBJanusTableWrapper) : Prop :=
  wrapperReady w /\
  w.exactCAMBFork /\
  w.boltzmannEquationsModifiedInSolver /\
  w.uncompressedPlanckLikelihoodUsed

theorem post_camb_wrapper_without_exact_fork_blocks_direct_likelihood
    (w : CAMBJanusTableWrapper)
    (_hWrapper : wrapperReady w)
    (hNoFork : Not w.exactCAMBFork) :
    Not (directCMBLikelihoodReady w) := by
  intro h
  exact hNoFork h.right.left

theorem wrapper_ready_from_backend_and_tables
    (w : CAMBJanusTableWrapper)
    (hBackend : w.backendSolverRun)
    (hTables : w.janusModifiedGravityTablesConsumed) :
    wrapperReady w := by
  exact And.intro hBackend hTables

end P0EFTCMBCAMBJanusTableWrapper
end JanusFormal

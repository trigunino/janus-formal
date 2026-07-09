namespace JanusFormal
namespace P0EFTCMBCAMBExactForkSmoke

set_option autoImplicit false

structure CAMBExactForkSmoke where
  forkDLLExists : Prop
  forkCAMBImported : Prop
  exactCAMBForkBuilt : Prop
  boltzmannEquationsModifiedInSolver : Prop
  janusSigmaHookCompiled : Prop
  uncompressedPlanckLikelihoodUsed : Prop

def exactForkSmokeReady (s : CAMBExactForkSmoke) : Prop :=
  s.forkDLLExists /\
  s.forkCAMBImported /\
  s.exactCAMBForkBuilt /\
  s.boltzmannEquationsModifiedInSolver /\
  s.janusSigmaHookCompiled

def directCMBReady (s : CAMBExactForkSmoke) : Prop :=
  exactForkSmokeReady s /\
  s.uncompressedPlanckLikelihoodUsed

theorem exact_fork_without_planck_likelihood_still_blocks_direct_cmb
    (s : CAMBExactForkSmoke)
    (_hFork : exactForkSmokeReady s)
    (hNoPlanck : Not s.uncompressedPlanckLikelihoodUsed) :
    Not (directCMBReady s) := by
  intro h
  exact hNoPlanck h.right

end P0EFTCMBCAMBExactForkSmoke
end JanusFormal

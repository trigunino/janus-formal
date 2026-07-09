namespace JanusFormal
namespace P0EFTCMBCAMBForkPatchScaffold

set_option autoImplicit false

structure CAMBForkPatchScaffold where
  patchScaffoldWritten : Prop
  fortranHookScaffoldWritten : Prop
  pythonTableHookWritten : Prop
  exactCAMBForkBuilt : Prop
  boltzmannEquationsModifiedInSolver : Prop
  directPlanckLikelihoodUsed : Prop

def scaffoldReady (s : CAMBForkPatchScaffold) : Prop :=
  s.patchScaffoldWritten /\
  s.fortranHookScaffoldWritten /\
  s.pythonTableHookWritten

def directCMBReady (s : CAMBForkPatchScaffold) : Prop :=
  scaffoldReady s /\
  s.exactCAMBForkBuilt /\
  s.boltzmannEquationsModifiedInSolver /\
  s.directPlanckLikelihoodUsed

theorem scaffold_without_exact_fork_blocks_direct_cmb
    (s : CAMBForkPatchScaffold)
    (_hScaffold : scaffoldReady s)
    (hNoFork : Not s.exactCAMBForkBuilt) :
    Not (directCMBReady s) := by
  intro h
  exact hNoFork h.right.left

theorem scaffold_ready_from_written_hooks
    (s : CAMBForkPatchScaffold)
    (hPatch : s.patchScaffoldWritten)
    (hFortran : s.fortranHookScaffoldWritten)
    (hPython : s.pythonTableHookWritten) :
    scaffoldReady s := by
  exact And.intro hPatch (And.intro hFortran hPython)

end P0EFTCMBCAMBForkPatchScaffold
end JanusFormal

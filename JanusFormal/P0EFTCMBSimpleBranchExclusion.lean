namespace JanusFormal
namespace P0EFTCMBSimpleBranchExclusion

set_option autoImplicit false

structure CMBSimpleBranchExclusion where
  freeNeffCarrierExcluded : Prop
  backgroundOnlyGeffExcluded : Prop
  coherentImmirziPatchExcluded : Prop
  newPrimordialPhysicsDerived : Prop

def simpleBranchExcluded (s : CMBSimpleBranchExclusion) : Prop :=
  s.freeNeffCarrierExcluded /\
  s.backgroundOnlyGeffExcluded /\
  s.coherentImmirziPatchExcluded

def fullNoFitReadyAfterCMB (s : CMBSimpleBranchExclusion) : Prop :=
  simpleBranchExcluded s /\
  s.newPrimordialPhysicsDerived

theorem planck_excludes_tested_simple_branch
    (s : CMBSimpleBranchExclusion)
    (hNeff : s.freeNeffCarrierExcluded)
    (hGeff : s.backgroundOnlyGeffExcluded)
    (hPatch : s.coherentImmirziPatchExcluded) :
    simpleBranchExcluded s := by
  exact And.intro hNeff (And.intro hGeff hPatch)

theorem missing_new_primordial_physics_blocks_no_fit
    (s : CMBSimpleBranchExclusion)
    (_hExcluded : simpleBranchExcluded s)
    (hMissing : Not s.newPrimordialPhysicsDerived) :
    Not (fullNoFitReadyAfterCMB s) := by
  intro h
  exact hMissing h.right

end P0EFTCMBSimpleBranchExclusion
end JanusFormal

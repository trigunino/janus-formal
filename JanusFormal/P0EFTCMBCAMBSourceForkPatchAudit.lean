namespace JanusFormal
namespace P0EFTCMBCAMBSourceForkPatchAudit

set_option autoImplicit false

structure CAMBSourceForkPatchAudit where
  sourceClonePresent : Prop
  fortranHookPresent : Prop
  makefileRegistered : Prop
  equationsImportsHook : Prop
  weylTransferPatched : Prop
  lensingSourcePatched : Prop
  poissonPhiPatched : Prop
  soundSpeedPatched : Prop
  opacityPatched : Prop
  gfortranAvailable : Prop
  exactCAMBForkBuilt : Prop

def sourcePatchApplied (a : CAMBSourceForkPatchAudit) : Prop :=
  a.sourceClonePresent /\
  a.fortranHookPresent /\
  a.makefileRegistered /\
  a.equationsImportsHook /\
  a.weylTransferPatched /\
  a.lensingSourcePatched /\
  a.poissonPhiPatched /\
  a.soundSpeedPatched /\
  a.opacityPatched

def exactForkReady (a : CAMBSourceForkPatchAudit) : Prop :=
  sourcePatchApplied a /\
  a.gfortranAvailable /\
  a.exactCAMBForkBuilt

theorem patch_without_built_fork_blocks_exact_ready
    (a : CAMBSourceForkPatchAudit)
    (_hPatch : sourcePatchApplied a)
    (hNoBuild : Not a.exactCAMBForkBuilt) :
    Not (exactForkReady a) := by
  intro h
  exact hNoBuild h.right.right

theorem source_patch_applied_from_components
    (a : CAMBSourceForkPatchAudit)
    (hClone : a.sourceClonePresent)
    (hHook : a.fortranHookPresent)
    (hMake : a.makefileRegistered)
    (hImport : a.equationsImportsHook)
    (hWeyl : a.weylTransferPatched)
    (hLens : a.lensingSourcePatched)
    (hPhi : a.poissonPhiPatched)
    (hCs2 : a.soundSpeedPatched)
    (hOpacity : a.opacityPatched) :
    sourcePatchApplied a := by
  exact And.intro hClone
    (And.intro hHook
      (And.intro hMake
        (And.intro hImport
          (And.intro hWeyl
            (And.intro hLens
              (And.intro hPhi
                (And.intro hCs2 hOpacity)))))))

end P0EFTCMBCAMBSourceForkPatchAudit
end JanusFormal

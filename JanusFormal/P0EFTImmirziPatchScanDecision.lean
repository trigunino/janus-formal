namespace JanusFormal
namespace P0EFTImmirziPatchScanDecision

set_option autoImplicit false

structure ImmirziPatchScanDecision where
  miniScanRun : Prop
  noAcceptedPoint : Prop
  previousSingleGateSuperseded : Prop

def simpleImmirziBranchExcluded (d : ImmirziPatchScanDecision) : Prop :=
  d.miniScanRun /\
  d.noAcceptedPoint /\
  d.previousSingleGateSuperseded

theorem mini_scan_excludes_simple_branch
    (d : ImmirziPatchScanDecision)
    (hRun : d.miniScanRun)
    (hNo : d.noAcceptedPoint)
    (hSuperseded : d.previousSingleGateSuperseded) :
    simpleImmirziBranchExcluded d := by
  exact And.intro hRun (And.intro hNo hSuperseded)

end P0EFTImmirziPatchScanDecision
end JanusFormal

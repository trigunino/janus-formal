namespace JanusFormal
namespace P0EFTPrimordialThetaScanDecision

set_option autoImplicit false

structure PrimordialThetaScanDecision where
  thetaScanRun : Prop
  neutralThetaBest : Prop
  nonzeroThetaImprovesPlanck : Prop

def wardSingleModeBranchExcluded (d : PrimordialThetaScanDecision) : Prop :=
  d.thetaScanRun /\
  d.neutralThetaBest /\
  Not d.nonzeroThetaImprovesPlanck

theorem neutral_best_excludes_single_mode_branch
    (d : PrimordialThetaScanDecision)
    (hRun : d.thetaScanRun)
    (hNeutral : d.neutralThetaBest)
    (hNoImprove : Not d.nonzeroThetaImprovesPlanck) :
    wardSingleModeBranchExcluded d := by
  exact And.intro hRun (And.intro hNeutral hNoImprove)

end P0EFTPrimordialThetaScanDecision
end JanusFormal

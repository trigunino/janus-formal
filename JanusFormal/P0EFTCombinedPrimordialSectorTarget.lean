namespace JanusFormal
namespace P0EFTCombinedPrimordialSectorTarget

set_option autoImplicit false

structure CombinedPrimordialSectorTarget where
  highLAndLowEResidualDominates : Prop
  otherPlanckChannelsAlreadyExceedStrictBudget : Prop
  coupledPrimordialLowESectorDerived : Prop
  lowLTTLensingSectorDerived : Prop

def requiresCoupledCMBPhysics (t : CombinedPrimordialSectorTarget) : Prop :=
  t.highLAndLowEResidualDominates /\
  t.otherPlanckChannelsAlreadyExceedStrictBudget

def cmbNoFitReadyAfterCombinedTarget (t : CombinedPrimordialSectorTarget) : Prop :=
  requiresCoupledCMBPhysics t /\
  t.coupledPrimordialLowESectorDerived /\
  t.lowLTTLensingSectorDerived

theorem combined_sector_required
    (t : CombinedPrimordialSectorTarget)
    (hMain : t.highLAndLowEResidualDominates)
    (hFloor : t.otherPlanckChannelsAlreadyExceedStrictBudget) :
    requiresCoupledCMBPhysics t := by
  exact And.intro hMain hFloor

theorem missing_combined_sector_blocks_no_fit
    (t : CombinedPrimordialSectorTarget)
    (_hReq : requiresCoupledCMBPhysics t)
    (hMissing : Not t.coupledPrimordialLowESectorDerived) :
    Not (cmbNoFitReadyAfterCombinedTarget t) := by
  intro h
  exact hMissing h.right.left

end P0EFTCombinedPrimordialSectorTarget
end JanusFormal

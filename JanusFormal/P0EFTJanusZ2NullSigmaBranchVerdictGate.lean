namespace JanusFormal
namespace P0EFTJanusZ2NullSigmaBranchVerdictGate

set_option autoImplicit false

structure NullSigmaBranchVerdictGate where
  boundaryVariablesReady : Prop
  bulkDensityVariationReduced : Prop
  canonicalPTJointReady : Prop
  plusSideTransverseCurvatureComputed : Prop
  transverseCurvatureJumpDerived : Prop
  nullJunctionBalanceReady : Prop
  nullBranchExhaustedWithoutSparadrap : Prop
  promoteNullShellModel : Prop
  chapter67RegularPTTransferSurfaceAvailable : Prop
  regularHKReopenAllowedOn67Route : Prop

def nullBranchReducedDataReady
    (g : NullSigmaBranchVerdictGate) : Prop :=
  g.boundaryVariablesReady /\
  g.bulkDensityVariationReduced /\
  g.canonicalPTJointReady /\
  g.plusSideTransverseCurvatureComputed

theorem null_branch_promotion_requires_curvature_jump
    (g : NullSigmaBranchVerdictGate)
    (hPromote : g.promoteNullShellModel)
    (hNeeds : g.promoteNullShellModel -> g.transverseCurvatureJumpDerived) :
    g.transverseCurvatureJumpDerived := by
  exact hNeeds hPromote

theorem regular_route_is_separate_from_null_junction
    (g : NullSigmaBranchVerdictGate)
    (hRoute : g.chapter67RegularPTTransferSurfaceAvailable)
    (hRegular : g.chapter67RegularPTTransferSurfaceAvailable -> g.regularHKReopenAllowedOn67Route) :
    g.regularHKReopenAllowedOn67Route := by
  exact hRegular hRoute

end P0EFTJanusZ2NullSigmaBranchVerdictGate
end JanusFormal

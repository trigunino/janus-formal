namespace JanusFormal
namespace P0EFTJanusEarlyTimeSisterBranchRulerGate

set_option autoImplicit false

structure EarlyTimeSisterBranchRulerGate where
  separateEarlyTimeBranchDeclared : Prop
  branchReachesDragDomain : Prop
  lateToEarlyMatchingConditionDerived : Prop
  preDragHJDerived : Prop
  noQ0BoundaryFit : Prop
  routeClosed : Prop

def sisterBranchRouteBlocked (g : EarlyTimeSisterBranchRulerGate) : Prop :=
  g.separateEarlyTimeBranchDeclared /\
  g.branchReachesDragDomain /\
  Not g.lateToEarlyMatchingConditionDerived /\
  Not g.preDragHJDerived /\
  g.noQ0BoundaryFit /\
  Not g.routeClosed

theorem sister_branch_route_needs_matching_and_predrag_hubble
    (g : EarlyTimeSisterBranchRulerGate)
    (h : sisterBranchRouteBlocked g) :
    Not g.routeClosed := by
  exact h.2.2.2.2.2

end P0EFTJanusEarlyTimeSisterBranchRulerGate
end JanusFormal

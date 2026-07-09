namespace JanusFormal
namespace P0EFTCMBBranchDecision

set_option autoImplicit false

structure CMBBranchDecision where
  routeAFreeNeffExcluded : Prop
  routeBBackgroundOnlyExcluded : Prop
  consistentImmirziPerturbationsDerived : Prop

def simpleCMBBranchesExcluded (d : CMBBranchDecision) : Prop :=
  d.routeAFreeNeffExcluded /\
  d.routeBBackgroundOnlyExcluded

def cmbRequiresPerturbativeImmirzi (d : CMBBranchDecision) : Prop :=
  simpleCMBBranchesExcluded d /\
  Not d.consistentImmirziPerturbationsDerived

def cmbBranchNoFitReady (d : CMBBranchDecision) : Prop :=
  simpleCMBBranchesExcluded d /\
  d.consistentImmirziPerturbationsDerived

theorem simple_routes_excluded_from_gates
    (d : CMBBranchDecision)
    (hA : d.routeAFreeNeffExcluded)
    (hB : d.routeBBackgroundOnlyExcluded) :
    simpleCMBBranchesExcluded d := by
  exact And.intro hA hB

theorem missing_immirzi_perturbations_blocks_no_fit
    (d : CMBBranchDecision)
    (_hSimple : simpleCMBBranchesExcluded d)
    (hMissing : Not d.consistentImmirziPerturbationsDerived) :
    Not (cmbBranchNoFitReady d) := by
  intro h
  exact hMissing h.right

end P0EFTCMBBranchDecision
end JanusFormal

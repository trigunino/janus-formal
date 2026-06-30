import JanusFormal.P0EFTFriedmannMatterClosure

namespace JanusFormal
namespace P0EFTPhysicalBranchScan

set_option autoImplicit false

structure PhysicalBranchScan where
  originalBranchExcluded : Prop
  atanhDomainFilterApplied : Prop
  matterPositivityFilterApplied : Prop
  physicalBranchFound : Prop
  physicalBranchSatisfiesFriedmannMatter : Prop
  fullPredictionMayUseSelectedBranch : Prop

def scanFiltersValid (s : PhysicalBranchScan) : Prop :=
  s.originalBranchExcluded /\
  s.atanhDomainFilterApplied /\
  s.matterPositivityFilterApplied

def physicalBranchReady (s : PhysicalBranchScan) : Prop :=
  scanFiltersValid s /\
  s.physicalBranchFound /\
  s.physicalBranchSatisfiesFriedmannMatter

def selectedBranchPredictionReady (s : PhysicalBranchScan) : Prop :=
  physicalBranchReady s /\ s.fullPredictionMayUseSelectedBranch

theorem branch_scan_filters_are_valid
    (s : PhysicalBranchScan)
    (hOrig : s.originalBranchExcluded)
    (hAtanh : s.atanhDomainFilterApplied)
    (hMatter : s.matterPositivityFilterApplied) :
    scanFiltersValid s := by
  exact And.intro hOrig (And.intro hAtanh hMatter)

theorem missing_physical_branch_blocks_selected_prediction
    (s : PhysicalBranchScan)
    (hMissing : Not s.physicalBranchFound) :
    Not (physicalBranchReady s) := by
  intro h
  exact hMissing h.right.left

theorem physical_branch_closes_scan_gate
    (s : PhysicalBranchScan)
    (hFilters : scanFiltersValid s)
    (hFound : s.physicalBranchFound)
    (hFriedmann : s.physicalBranchSatisfiesFriedmannMatter) :
    physicalBranchReady s := by
  exact And.intro hFilters (And.intro hFound hFriedmann)

end P0EFTPhysicalBranchScan
end JanusFormal

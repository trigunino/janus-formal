import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTCosmologicalChi2Calculator

namespace JanusFormal
namespace P0EFTCosmologicalMiniScan

set_option autoImplicit false

structure CosmologicalMiniScan where
  physicalBranchesScored : Prop
  bestUnitAmplitudeBranchFound : Prop
  bestFreeAmplitudeBranchFound : Prop
  unitAmplitudeAcceptanceCriterionPassed : Prop
  bestFitBranchLegitimateForPrediction : Prop

def miniScanComputed (s : CosmologicalMiniScan) : Prop :=
  s.physicalBranchesScored /\
  s.bestUnitAmplitudeBranchFound /\
  s.bestFreeAmplitudeBranchFound

def noFitBranchAccepted (s : CosmologicalMiniScan) : Prop :=
  miniScanComputed s /\
  s.unitAmplitudeAcceptanceCriterionPassed /\
  s.bestFitBranchLegitimateForPrediction

theorem mini_scan_computes_best_branches
    (s : CosmologicalMiniScan)
    (hScore : s.physicalBranchesScored)
    (hUnit : s.bestUnitAmplitudeBranchFound)
    (hFree : s.bestFreeAmplitudeBranchFound) :
    miniScanComputed s := by
  exact And.intro hScore (And.intro hUnit hFree)

theorem failed_unit_acceptance_blocks_no_fit_branch
    (s : CosmologicalMiniScan)
    (hFail : Not s.unitAmplitudeAcceptanceCriterionPassed) :
    Not (noFitBranchAccepted s) := by
  intro h
  exact hFail h.right.left

end P0EFTCosmologicalMiniScan
end JanusFormal

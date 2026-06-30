import JanusFormal.P0EFTUVInitialConditionScan

namespace JanusFormal
namespace P0EFTHolstImmirziGrowthSolver

set_option autoImplicit false

structure HolstImmirziGrowthSolver where
  holstTermActivated : Prop
  immirziRadionDependenceEncoded : Prop
  dynamicMuCoefficientDefined : Prop
  holstBranchesScored : Prop
  acceptedHolstBranchFound : Prop
  immirziLawDerivedGeometrically : Prop

def holstScanStructured (h : HolstImmirziGrowthSolver) : Prop :=
  h.holstTermActivated /\
  h.immirziRadionDependenceEncoded /\
  h.dynamicMuCoefficientDefined /\
  h.holstBranchesScored

def holstNoFitCandidateReady (h : HolstImmirziGrowthSolver) : Prop :=
  holstScanStructured h /\
  h.acceptedHolstBranchFound /\
  h.immirziLawDerivedGeometrically

theorem holst_immirzi_scan_is_structured
    (h : HolstImmirziGrowthSolver)
    (hHolst : h.holstTermActivated)
    (hImmirzi : h.immirziRadionDependenceEncoded)
    (hMu : h.dynamicMuCoefficientDefined)
    (hScan : h.holstBranchesScored) :
    holstScanStructured h := by
  exact And.intro hHolst (And.intro hImmirzi (And.intro hMu hScan))

theorem underived_immirzi_law_blocks_no_fit_candidate
    (h : HolstImmirziGrowthSolver)
    (hMissing : Not h.immirziLawDerivedGeometrically) :
    Not (holstNoFitCandidateReady h) := by
  intro hReady
  exact hMissing hReady.right.right

end P0EFTHolstImmirziGrowthSolver
end JanusFormal

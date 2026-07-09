import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4LowTTComponentDiagnostic

namespace JanusFormal
namespace P0EFTJanusZ4ScalarSourceScan

set_option autoImplicit false

structure ScalarSourceScan where
  nativeZ4SolverUsed : Prop
  compressedLCDMParametersNotUsed : Prop
  officialPlanckLikelihoodNotClaimed : Prop
  potentialHorizonScaleScanned : Prop
  lowTTShapeProxyReported : Prop
  highlTTShapeProxyReported : Prop
  swIswFractionsReported : Prop
  activeModelIncluded : Prop

def scalarSourceScanReady (s : ScalarSourceScan) : Prop :=
  s.nativeZ4SolverUsed /\
  s.compressedLCDMParametersNotUsed /\
  s.officialPlanckLikelihoodNotClaimed /\
  s.potentialHorizonScaleScanned /\
  s.lowTTShapeProxyReported /\
  s.highlTTShapeProxyReported /\
  s.swIswFractionsReported /\
  s.activeModelIncluded

theorem scalar_source_scan_is_not_planck_gate
    (s : ScalarSourceScan)
    (h : scalarSourceScanReady s) :
    s.officialPlanckLikelihoodNotClaimed := by
  exact h.right.right.left

theorem scalar_source_scan_links_low_and_high_tt
    (s : ScalarSourceScan)
    (h : scalarSourceScanReady s) :
    s.lowTTShapeProxyReported /\ s.highlTTShapeProxyReported /\ s.swIswFractionsReported := by
  exact ⟨h.right.right.right.right.left,
    h.right.right.right.right.right.left,
    h.right.right.right.right.right.right.left⟩

end P0EFTJanusZ4ScalarSourceScan
end JanusFormal

import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4PeakDampingDiagnostic

namespace JanusFormal
namespace P0EFTJanusZ4PolarizationSourceScan

set_option autoImplicit false

structure PolarizationSourceScan where
  nativeZ4SolverUsed : Prop
  compressedLCDMParametersNotUsed : Prop
  officialPlanckLikelihoodNotClaimed : Prop
  shearSourceCompared : Prop
  quadrupoleSourceCompared : Prop
  hybridSourceCompared : Prop
  activeSourceIsShear : Prop
  quadrupoleKeptAsCandidate : Prop
  fullPolarizationHierarchyStillRequired : Prop

def polarizationSourceScanReady (s : PolarizationSourceScan) : Prop :=
  s.nativeZ4SolverUsed /\
  s.compressedLCDMParametersNotUsed /\
  s.officialPlanckLikelihoodNotClaimed /\
  s.shearSourceCompared /\
  s.quadrupoleSourceCompared /\
  s.hybridSourceCompared /\
  s.activeSourceIsShear /\
  s.quadrupoleKeptAsCandidate /\
  s.fullPolarizationHierarchyStillRequired

theorem scan_does_not_claim_polarization_closure
    (s : PolarizationSourceScan)
    (h : polarizationSourceScanReady s) :
    s.fullPolarizationHierarchyStillRequired := by
  exact h.right.right.right.right.right.right.right.right

theorem scan_keeps_quadrupole_as_candidate_only
    (s : PolarizationSourceScan)
    (h : polarizationSourceScanReady s) :
    s.activeSourceIsShear /\ s.quadrupoleKeptAsCandidate := by
  exact ⟨h.right.right.right.right.right.right.left, h.right.right.right.right.right.right.right.left⟩

end P0EFTJanusZ4PolarizationSourceScan
end JanusFormal

import JanusFormal.Branches.CMBHistoricalDiagnostics.Gates.P0EFTHolstMembraneCoOptimisation
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTNiehYanAnomalyDerivation
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldHolonomyQuantization
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTGlobalTopologyClosureRequirements

namespace JanusFormal
namespace P0EFTHolstGeometricLock

set_option autoImplicit false

structure HolstGeometricLock where
  holstBranchObservationallyAccepted : Prop
  etaHIntegerLockCandidateEncoded : Prop
  aSigmaRationalLockCandidateEncoded : Prop
  etaHDerivedFromHolstNiehYanTrace : Prop
  aSigmaDerivedFromOrbifoldHolonomy : Prop
  fullCosmologyPredictionReadyConditionally : Prop
  fullCosmologyPredictionReadyNoFit : Prop

def holstLockCandidatesEncoded (h : HolstGeometricLock) : Prop :=
  h.holstBranchObservationallyAccepted /\
  h.etaHIntegerLockCandidateEncoded /\
  h.aSigmaRationalLockCandidateEncoded

def holstNoFitGeometricLockClosed (h : HolstGeometricLock) : Prop :=
  holstLockCandidatesEncoded h /\
  h.etaHDerivedFromHolstNiehYanTrace /\
  h.aSigmaDerivedFromOrbifoldHolonomy /\
  h.fullCosmologyPredictionReadyNoFit

theorem accepted_holst_branch_encodes_lock_candidates
    (h : HolstGeometricLock)
    (hObs : h.holstBranchObservationallyAccepted)
    (hEta : h.etaHIntegerLockCandidateEncoded)
    (hSigma : h.aSigmaRationalLockCandidateEncoded) :
    holstLockCandidatesEncoded h := by
  exact And.intro hObs (And.intro hEta hSigma)

theorem missing_eta_trace_derivation_blocks_no_fit_lock
    (h : HolstGeometricLock)
    (hMissing : Not h.etaHDerivedFromHolstNiehYanTrace) :
    Not (holstNoFitGeometricLockClosed h) := by
  intro hClosed
  exact hMissing hClosed.right.left

theorem missing_holonomy_derivation_blocks_no_fit_lock
    (h : HolstGeometricLock)
    (hMissing : Not h.aSigmaDerivedFromOrbifoldHolonomy) :
    Not (holstNoFitGeometricLockClosed h) := by
  intro hClosed
  exact hMissing hClosed.right.right.left

theorem no_fit_lock_closes_after_geometric_derivations
    (h : HolstGeometricLock)
    (hCandidates : holstLockCandidatesEncoded h)
    (hEta : h.etaHDerivedFromHolstNiehYanTrace)
    (hSigma : h.aSigmaDerivedFromOrbifoldHolonomy)
    (hReady : h.fullCosmologyPredictionReadyNoFit) :
    holstNoFitGeometricLockClosed h := by
  exact And.intro hCandidates (And.intro hEta (And.intro hSigma hReady))

theorem local_trace_and_holonomy_identities_are_not_full_no_fit_proof
    (h : HolstGeometricLock)
    (etaLock : P0EFTNiehYanAnomalyDerivation.NiehYanTraceLock)
    (sigmaLock : P0EFTOrbifoldHolonomyQuantization.OrbifoldHolonomyLock)
    (_hEtaLocal : P0EFTNiehYanAnomalyDerivation.etaHPlusTwoClosed etaLock)
    (_hSigmaLocal :
      P0EFTOrbifoldHolonomyQuantization.threeASigmaMinusTwoClosed sigmaLock)
    (hMissingEta : Not h.etaHDerivedFromHolstNiehYanTrace) :
    Not (holstNoFitGeometricLockClosed h) := by
  intro hClosed
  exact hMissingEta hClosed.right.left

theorem global_topology_open_blocks_holst_no_fit
    (h : HolstGeometricLock)
    (g : P0EFTGlobalTopologyClosureRequirements.GlobalTopologyClosure)
    (hMissing :
      Not (P0EFTGlobalTopologyClosureRequirements.globalTopologyClosed g)) :
    Not (holstNoFitGeometricLockClosed h /\ 
      P0EFTGlobalTopologyClosureRequirements.noFitTopologyReady g) := by
  intro closed
  exact hMissing closed.right.left

end P0EFTHolstGeometricLock
end JanusFormal

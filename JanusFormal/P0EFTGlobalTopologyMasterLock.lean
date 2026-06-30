import JanusFormal.P0EFTHolstGeometricLock
import JanusFormal.P0EFTAPSPinDiracKernelTrivialization
import JanusFormal.P0EFTAPSPinGlobalIndexClosure
import JanusFormal.P0EFTOrbifoldHolonomyFluxQuantization
import JanusFormal.P0EFTOrbifoldFluxIntegerTheorem
import JanusFormal.P0EFTOrbifoldFluxOrientationRule
import JanusFormal.P0EFTOrbifoldFluxQuantizationLaw
import JanusFormal.P0EFTOrbifoldHolonomyQuantumNormalization
import JanusFormal.P0EFTOrbifoldZ2HolonomyUnit
import JanusFormal.P0EFTOrbifoldZ2GroupLaw
import JanusFormal.P0EFTOrbifoldSingularCycleGenerator
import JanusFormal.P0EFTOrbifoldGeneratorHolonomyUnit
import JanusFormal.P0EFTOrbifoldSpinConnectionGaugeFix
import JanusFormal.P0EFTOrbifoldHolonomyQuantumNormalized
import JanusFormal.P0EFTOrbifoldNormalizedFluxInteger
import JanusFormal.P0EFTOrbifoldIntegerFluxLaw
import JanusFormal.P0EFTOrbifoldJanusOrientationRule

namespace JanusFormal
namespace P0EFTGlobalTopologyMasterLock

set_option autoImplicit false

structure GlobalTopologyMasterLock where
  apsPinScaffoldComplete : Prop
  orbifoldHolonomyScaffoldComplete : Prop
  localEtaLockClosed : Prop
  localASigmaLockClosed : Prop
  observationalHolstBranchAccepted : Prop
  apsGlobalTheoremProved : Prop
  orbifoldGlobalTheoremProved : Prop
  globalTopologyScaffoldComplete : Prop
  fullCosmologyPredictionReadyNoFit : Prop

def run9ScaffoldComplete (m : GlobalTopologyMasterLock) : Prop :=
  m.apsPinScaffoldComplete /\
  m.orbifoldHolonomyScaffoldComplete /\
  m.localEtaLockClosed /\
  m.localASigmaLockClosed /\
  m.observationalHolstBranchAccepted /\
  m.globalTopologyScaffoldComplete

def run9NoFitReady (m : GlobalTopologyMasterLock) : Prop :=
  run9ScaffoldComplete m /\
  m.apsGlobalTheoremProved /\
  m.orbifoldGlobalTheoremProved /\
  m.fullCosmologyPredictionReadyNoFit

theorem scaffold_complete_after_run7_run8
    (m : GlobalTopologyMasterLock)
    (hAPS : m.apsPinScaffoldComplete)
    (hOrbifold : m.orbifoldHolonomyScaffoldComplete)
    (hEta : m.localEtaLockClosed)
    (hSigma : m.localASigmaLockClosed)
    (hObs : m.observationalHolstBranchAccepted)
    (hScaffold : m.globalTopologyScaffoldComplete) :
    run9ScaffoldComplete m := by
  exact And.intro hAPS
    (And.intro hOrbifold
      (And.intro hEta
        (And.intro hSigma
          (And.intro hObs hScaffold))))

theorem open_aps_global_theorem_blocks_run9_no_fit
    (m : GlobalTopologyMasterLock)
    (hMissing : Not m.apsGlobalTheoremProved) :
    Not (run9NoFitReady m) := by
  intro h
  exact hMissing h.right.left

theorem open_orbifold_global_theorem_blocks_run9_no_fit
    (m : GlobalTopologyMasterLock)
    (hMissing : Not m.orbifoldGlobalTheoremProved) :
    Not (run9NoFitReady m) := by
  intro h
  exact hMissing h.right.right.left

theorem run9_no_fit_requires_both_global_theorems
    (m : GlobalTopologyMasterLock)
    (hScaffold : run9ScaffoldComplete m)
    (hAPS : m.apsGlobalTheoremProved)
    (hOrbifold : m.orbifoldGlobalTheoremProved)
    (hReady : m.fullCosmologyPredictionReadyNoFit) :
    run9NoFitReady m := by
  exact And.intro hScaffold (And.intro hAPS (And.intro hOrbifold hReady))

end P0EFTGlobalTopologyMasterLock
end JanusFormal

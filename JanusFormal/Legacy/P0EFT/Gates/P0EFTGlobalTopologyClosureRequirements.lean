import JanusFormal.Legacy.P0EFT.Gates.P0EFTNiehYanAnomalyDerivation
import JanusFormal.Legacy.P0EFT.Gates.P0EFTOrbifoldHolonomyQuantization

namespace JanusFormal
namespace P0EFTGlobalTopologyClosureRequirements

set_option autoImplicit false

structure GlobalTopologyClosure where
  localEtaIdentityClosed : Prop
  localASigmaIdentityClosed : Prop
  apsTraceNormalizationDerived : Prop
  orbifoldTwoToOneCoverDerived : Prop
  fullCosmologyPredictionReadyNoFit : Prop

def globalTopologyClosed (g : GlobalTopologyClosure) : Prop :=
  g.localEtaIdentityClosed /\
  g.localASigmaIdentityClosed /\
  g.apsTraceNormalizationDerived /\
  g.orbifoldTwoToOneCoverDerived

def noFitTopologyReady (g : GlobalTopologyClosure) : Prop :=
  globalTopologyClosed g /\ g.fullCosmologyPredictionReadyNoFit

theorem open_aps_normalization_blocks_no_fit
    (g : GlobalTopologyClosure)
    (hMissing : Not g.apsTraceNormalizationDerived) :
    Not (noFitTopologyReady g) := by
  intro h
  exact hMissing h.left.right.right.left

theorem open_orbifold_cover_blocks_no_fit
    (g : GlobalTopologyClosure)
    (hMissing : Not g.orbifoldTwoToOneCoverDerived) :
    Not (noFitTopologyReady g) := by
  intro h
  exact hMissing h.left.right.right.right

theorem topology_no_fit_ready_after_global_lemmas
    (g : GlobalTopologyClosure)
    (hLocalEta : g.localEtaIdentityClosed)
    (hLocalSigma : g.localASigmaIdentityClosed)
    (hAPS : g.apsTraceNormalizationDerived)
    (hCover : g.orbifoldTwoToOneCoverDerived)
    (hReady : g.fullCosmologyPredictionReadyNoFit) :
    noFitTopologyReady g := by
  exact And.intro
    (And.intro hLocalEta (And.intro hLocalSigma (And.intro hAPS hCover)))
    hReady

end P0EFTGlobalTopologyClosureRequirements
end JanusFormal

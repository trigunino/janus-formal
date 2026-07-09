namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOScaleFreeChi2Gate

set_option autoImplicit false

structure BAOScaleFreeChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  scaleFreeManifestAvailable : Prop
  scaleFreeBAOEvaluation : Prop
  baoChi2Evaluated : Prop
  sourceHashMatchesManifest : Prop
  officialDimensionalBAOGateUnblocked : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4ReuseUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def scaleFreeChi2ContractClosed
    (g : BAOScaleFreeChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.scaleFreeManifestAvailable /\
  g.scaleFreeBAOEvaluation /\
  g.baoChi2Evaluated /\
  g.sourceHashMatchesManifest /\
  ¬ g.officialDimensionalBAOGateUnblocked /\
  ¬ g.compressedPlanckLCDMRdUsed /\
  ¬ g.archivedZ4ReuseUsed /\
  ¬ g.phenomenologicalHolstBAOScanUsed /\
  ¬ g.observationalH0FitUsed /\
  g.gatePassed

theorem scale_free_chi2_does_not_unblock_dimensional_official_bao
    (g : BAOScaleFreeChi2Gate)
    (hClosed : scaleFreeChi2ContractClosed g) :
    ¬ g.officialDimensionalBAOGateUnblocked := by
  rcases hClosed with ⟨_, _, _, _, _, hBlocked, _, _, _, _, _⟩
  exact hBlocked

theorem scale_free_chi2_forbids_compressed_priors
    (g : BAOScaleFreeChi2Gate)
    (hClosed : scaleFreeChi2ContractClosed g) :
    ¬ g.compressedPlanckLCDMRdUsed ∧ ¬ g.archivedZ4ReuseUsed := by
  rcases hClosed with ⟨_, _, _, _, _, _, hNoPlanck, hNoZ4, _, _, _⟩
  exact ⟨hNoPlanck, hNoZ4⟩

end P0EFTJanusZ2SigmaBAOScaleFreeChi2Gate
end JanusFormal

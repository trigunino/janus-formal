namespace JanusFormal
namespace P0EFTJanusZ2PublishedBimetricFLRWToSigmaBridgeGate

set_option autoImplicit false

structure PublishedBimetricFLRWToSigmaBridgeGate where
  publishedInteractionSlotsReady : Prop
  determinantFactorsReady : Prop
  flrwReducedBianchiReady : Prop
  sectorRhoPressureOfAReady : Prop
  sectorNormalizationsDerived : Prop
  sigmaEmbeddingPullbackReady : Prop
  sigmaInducedMetricsReady : Prop
  sigmaExtrinsicCurvaturesReady : Prop
  sigmaStressFluxProjectionReady : Prop
  projectedBianchiJunctionReady : Prop
  observableEOfAReady : Prop
  copiedPublishedHOfA : Prop
  fittedSectorDensity : Prop
  forcedNGapToDensity : Prop

def honestBridgeReady (g : PublishedBimetricFLRWToSigmaBridgeGate) : Prop :=
  g.publishedInteractionSlotsReady /\
  g.determinantFactorsReady /\
  g.flrwReducedBianchiReady /\
  g.sectorRhoPressureOfAReady /\
  g.sectorNormalizationsDerived /\
  g.sigmaEmbeddingPullbackReady /\
  g.sigmaInducedMetricsReady /\
  g.sigmaExtrinsicCurvaturesReady /\
  g.sigmaStressFluxProjectionReady /\
  g.projectedBianchiJunctionReady /\
  Not g.copiedPublishedHOfA /\
  Not g.fittedSectorDensity /\
  Not g.forcedNGapToDensity

theorem honest_bridge_is_required_for_observable_E
    (g : PublishedBimetricFLRWToSigmaBridgeGate)
    (hNeeds : g.observableEOfAReady -> honestBridgeReady g) :
    g.observableEOfAReady -> honestBridgeReady g := by
  intro hE
  exact hNeeds hE

theorem missing_sigma_pullback_blocks_honest_bridge
    (g : PublishedBimetricFLRWToSigmaBridgeGate)
    (hMissing : Not g.sigmaEmbeddingPullbackReady) :
    Not (honestBridgeReady g) := by
  intro h
  rcases h with ⟨_, _, _, _, _, hSigma, _⟩
  exact hMissing hSigma

theorem no_shortcuts_are_part_of_bridge
    (g : PublishedBimetricFLRWToSigmaBridgeGate)
    (h : honestBridgeReady g) :
    Not g.copiedPublishedHOfA /\ Not g.fittedSectorDensity /\ Not g.forcedNGapToDensity := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hNoCopy, hNoFit, hNoNGap⟩
  exact And.intro hNoCopy (And.intro hNoFit hNoNGap)

end P0EFTJanusZ2PublishedBimetricFLRWToSigmaBridgeGate
end JanusFormal

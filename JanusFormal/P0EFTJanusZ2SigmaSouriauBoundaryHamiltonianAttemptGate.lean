namespace JanusFormal
namespace P0EFTJanusZ2SigmaSouriauBoundaryHamiltonianAttemptGate

set_option autoImplicit false

structure SouriauBoundaryHamiltonianAttemptGate where
  momentMapChargeQSigmaDeclared : Prop
  deckInvariantChargeReduction : Prop
  absoluteOccupationFixed : Prop
  muSigmaAvailableFromExistingGeometry : Prop
  localDensityFromChargeAvailable : Prop
  metricVariationAvailable : Prop
  extrinsicCurvatureVariationAvailable : Prop
  alphaHFromSouriauHamiltonian : Prop
  alphaKFromSouriauHamiltonian : Prop
  closesECounterterm : Prop
  noObservationFitForMuSigma : Prop
  noGlobalChargeAsLocalDensityShortcut : Prop

def souriauGlobalChargeReady
    (g : SouriauBoundaryHamiltonianAttemptGate) : Prop :=
  g.momentMapChargeQSigmaDeclared /\
  g.deckInvariantChargeReduction /\
  g.noObservationFitForMuSigma /\
  g.noGlobalChargeAsLocalDensityShortcut

theorem missing_local_density_blocks_metric_variation
    (g : SouriauBoundaryHamiltonianAttemptGate)
    (hMissingDensity : Not g.localDensityFromChargeAvailable)
    (hVariationNeedsDensity :
      g.metricVariationAvailable -> g.localDensityFromChargeAvailable) :
    Not g.metricVariationAvailable := by
  intro hVar
  exact hMissingDensity (hVariationNeedsDensity hVar)

theorem global_charge_alone_does_not_give_alpha_h
    (g : SouriauBoundaryHamiltonianAttemptGate)
    (_hCharge : souriauGlobalChargeReady g)
    (hMissingMetricVariation : Not g.metricVariationAvailable)
    (hAlphaNeedsMetricVariation :
      g.alphaHFromSouriauHamiltonian -> g.metricVariationAvailable) :
    Not g.alphaHFromSouriauHamiltonian := by
  intro hAlpha
  exact hMissingMetricVariation (hAlphaNeedsMetricVariation hAlpha)

theorem global_charge_alone_does_not_give_alpha_k
    (g : SouriauBoundaryHamiltonianAttemptGate)
    (_hCharge : souriauGlobalChargeReady g)
    (hMissingKVariation : Not g.extrinsicCurvatureVariationAvailable)
    (hAlphaNeedsKVariation :
      g.alphaKFromSouriauHamiltonian -> g.extrinsicCurvatureVariationAvailable) :
    Not g.alphaKFromSouriauHamiltonian := by
  intro hAlpha
  exact hMissingKVariation (hAlphaNeedsKVariation hAlpha)

theorem missing_alpha_h_blocks_counterterm_closure
    (g : SouriauBoundaryHamiltonianAttemptGate)
    (hMissingAlpha : Not g.alphaHFromSouriauHamiltonian)
    (hCountertermNeedsAlpha :
      g.closesECounterterm -> g.alphaHFromSouriauHamiltonian) :
    Not g.closesECounterterm := by
  intro hClosed
  exact hMissingAlpha (hCountertermNeedsAlpha hClosed)

end P0EFTJanusZ2SigmaSouriauBoundaryHamiltonianAttemptGate
end JanusFormal

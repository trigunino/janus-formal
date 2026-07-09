namespace JanusFormal
namespace P0EFTJanusZ2SigmaSouriauBoundaryMomentMapAlphaRouteGate

set_option autoImplicit false

structure SouriauBoundaryMomentMapAlphaRouteGate where
  souriauPhaseSpaceRouteAvailable : Prop
  boundaryMomentMapDeclared : Prop
  sigmaHamiltonianBoundaryFunctionalAvailable : Prop
  momentMapChargeConserved : Prop
  momentMapVariationToAlphaHAvailable : Prop
  momentMapVariationToAlphaKAvailable : Prop
  closesECounterterm : Prop
  closesSigmaAlphaH : Prop
  negativeEnergyOrientationSupported : Prop
  negativeThermodynamicDensityPostulated : Prop
  freeSurfaceDensityAdded : Prop

def souriauChargeLedgerReady
    (g : SouriauBoundaryMomentMapAlphaRouteGate) : Prop :=
  g.souriauPhaseSpaceRouteAvailable /\
  g.boundaryMomentMapDeclared /\
  g.momentMapChargeConserved /\
  g.negativeEnergyOrientationSupported /\
  Not g.negativeThermodynamicDensityPostulated /\
  Not g.freeSurfaceDensityAdded

theorem missing_boundary_hamiltonian_blocks_alpha_route
    (g : SouriauBoundaryMomentMapAlphaRouteGate)
    (hMissingH : Not g.sigmaHamiltonianBoundaryFunctionalAvailable)
    (hAlphaNeedsH :
      g.momentMapVariationToAlphaHAvailable ->
        g.sigmaHamiltonianBoundaryFunctionalAvailable)
    (hKNeedsH :
      g.momentMapVariationToAlphaKAvailable ->
        g.sigmaHamiltonianBoundaryFunctionalAvailable) :
    Not g.momentMapVariationToAlphaHAvailable /\
      Not g.momentMapVariationToAlphaKAvailable := by
  exact And.intro
    (fun hAlpha => hMissingH (hAlphaNeedsH hAlpha))
    (fun hK => hMissingH (hKNeedsH hK))

theorem souriau_charge_ledger_alone_does_not_close_counterterm
    (g : SouriauBoundaryMomentMapAlphaRouteGate)
    (_hLedger : souriauChargeLedgerReady g)
    (hMissingAlpha : Not g.momentMapVariationToAlphaHAvailable)
    (hCountertermNeedsAlpha :
      g.closesECounterterm -> g.momentMapVariationToAlphaHAvailable) :
    Not g.closesECounterterm := by
  intro hClosed
  exact hMissingAlpha (hCountertermNeedsAlpha hClosed)

theorem souriau_charge_ledger_alone_does_not_close_sigma_alpha_h
    (g : SouriauBoundaryMomentMapAlphaRouteGate)
    (_hLedger : souriauChargeLedgerReady g)
    (hMissingAlpha : Not g.momentMapVariationToAlphaHAvailable)
    (hSigmaNeedsAlpha :
      g.closesSigmaAlphaH -> g.momentMapVariationToAlphaHAvailable) :
    Not g.closesSigmaAlphaH := by
  intro hClosed
  exact hMissingAlpha (hSigmaNeedsAlpha hClosed)

end P0EFTJanusZ2SigmaSouriauBoundaryMomentMapAlphaRouteGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2PublishedInteractionSlotsGate

set_option autoImplicit false

structure PublishedInteractionSlotsGate where
  publishedBimetricActionAvailable : Prop
  plusSameSectorSlotDeclared : Prop
  minusSameSectorSlotDeclared : Prop
  minusToPlusInteractionSlotDeclared : Prop
  plusToMinusInteractionSlotDeclared : Prop
  determinantBridgeFactorsDeclared : Prop
  bianchiObligationsDeclared : Prop
  completeNonlinearInteractionTensorAvailable : Prop
  reducedBianchiClosureReady : Prop
  sigmaSourceAvailable : Prop
  canTransportToSigma : Prop
  rhoEffCollapseUsed : Prop
  negativeThermodynamicDensityPostulated : Prop

def publishedSlotsReady (g : PublishedInteractionSlotsGate) : Prop :=
  g.publishedBimetricActionAvailable /\
  g.plusSameSectorSlotDeclared /\
  g.minusSameSectorSlotDeclared /\
  g.minusToPlusInteractionSlotDeclared /\
  g.plusToMinusInteractionSlotDeclared /\
  g.determinantBridgeFactorsDeclared /\
  g.bianchiObligationsDeclared /\
  Not g.rhoEffCollapseUsed /\
  Not g.negativeThermodynamicDensityPostulated

theorem transport_to_sigma_requires_reduced_bianchi_or_sigma_source
    (g : PublishedInteractionSlotsGate)
    (_h : publishedSlotsReady g)
    (hTransportNeeds :
      g.canTransportToSigma ->
        g.reducedBianchiClosureReady /\ g.sigmaSourceAvailable) :
    g.canTransportToSigma -> g.reducedBianchiClosureReady /\ g.sigmaSourceAvailable := by
  intro hTransport
  exact hTransportNeeds hTransport

theorem missing_reduced_bianchi_blocks_sigma_transport
    (g : PublishedInteractionSlotsGate)
    (_h : publishedSlotsReady g)
    (hMissing : Not g.reducedBianchiClosureReady)
    (hTransportNeeds :
      g.canTransportToSigma ->
        g.reducedBianchiClosureReady /\ g.sigmaSourceAvailable) :
    Not g.canTransportToSigma := by
  intro hTransport
  exact hMissing (hTransportNeeds hTransport).left

end P0EFTJanusZ2PublishedInteractionSlotsGate
end JanusFormal

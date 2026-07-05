namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpinorQuotientDescentEquivarianceGate

set_option autoImplicit false

structure SpinorQuotientDescentEquivarianceGate where
  quotientSectionDescentBibliographyChecked : Prop
  doubleCoverDeckActionDeclared : Prop
  equivariantBundleDescentTheoremImported : Prop
  pinorDoubleCoverSheetExchangeBibliographyChecked : Prop
  localUZ2SigmaImported : Prop
  observationalFitForbidden : Prop
  resolvedTunnelPinLiftReady : Prop
  deckActionLiftedToSpinorBundle : Prop
  physicalSpinorDeclaredAsQuotientSection : Prop
  quotientSectionLiftsEquivariantly : Prop
  physicalSpinorEquivarianceDerived : Prop

def ledgerDeclared (g : SpinorQuotientDescentEquivarianceGate) : Prop :=
  g.quotientSectionDescentBibliographyChecked /\
  g.doubleCoverDeckActionDeclared /\
  g.equivariantBundleDescentTheoremImported /\
  g.pinorDoubleCoverSheetExchangeBibliographyChecked /\
  g.localUZ2SigmaImported /\
  g.observationalFitForbidden

def ready (g : SpinorQuotientDescentEquivarianceGate) : Prop :=
  ledgerDeclared g /\
  g.resolvedTunnelPinLiftReady /\
  g.deckActionLiftedToSpinorBundle /\
  g.physicalSpinorDeclaredAsQuotientSection /\
  g.quotientSectionLiftsEquivariantly /\
  g.physicalSpinorEquivarianceDerived

theorem ready_requires_resolved_tunnel_pin_lift
    (g : SpinorQuotientDescentEquivarianceGate)
    (h : ready g) :
    g.resolvedTunnelPinLiftReady := by
  exact h.2.1

theorem no_descent_equivariance_without_pin_lift
    (g : SpinorQuotientDescentEquivarianceGate)
    (_h : ledgerDeclared g)
    (hMissing : Not g.resolvedTunnelPinLiftReady) :
    Not (ready g) := by
  intro hReady
  exact hMissing hReady.2.1

end P0EFTJanusZ2SigmaSpinorQuotientDescentEquivarianceGate
end JanusFormal

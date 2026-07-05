namespace JanusFormal
namespace P0EFTJanusZ2SigmaHolstNiehYanComponentFromInputsGate

set_option autoImplicit false

structure HolstNiehYanComponentFromInputsGate where
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  activeHolstNiehYanFLRWReduction : Prop
  aGridDeclared : Prop
  componentProvenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  componentOutputWritten : Prop

def canWriteHolstNiehYanComponents
    (g : HolstNiehYanComponentFromInputsGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.activeHolstNiehYanFLRWReduction /\
  g.aGridDeclared /\
  g.componentProvenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden

theorem holst_components_require_active_reduction
    (g : HolstNiehYanComponentFromInputsGate)
    (h : canWriteHolstNiehYanComponents g) :
    g.activeHolstNiehYanFLRWReduction := by
  exact h.2.2.1

end P0EFTJanusZ2SigmaHolstNiehYanComponentFromInputsGate
end JanusFormal

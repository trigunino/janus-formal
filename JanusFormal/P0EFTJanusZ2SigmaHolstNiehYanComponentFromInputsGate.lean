namespace JanusFormal
namespace P0EFTJanusZ2SigmaHolstNiehYanComponentFromInputsGate

set_option autoImplicit false

structure HolstNiehYanComponentFromInputsGate where
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  activeHolstNiehYanFLRWReduction : Prop
  torsionlessRadialZeroIdentityReady : Prop
  aGridDeclared : Prop
  componentProvenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  componentOutputWritten : Prop

def holstComponentInputRouteReady
    (g : HolstNiehYanComponentFromInputsGate) : Prop :=
  g.activeHolstNiehYanFLRWReduction \/ g.torsionlessRadialZeroIdentityReady

def canWriteHolstNiehYanComponents
    (g : HolstNiehYanComponentFromInputsGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  holstComponentInputRouteReady g /\
  g.aGridDeclared /\
  g.componentProvenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden

theorem holst_components_require_active_reduction_or_radial_zero_identity
    (g : HolstNiehYanComponentFromInputsGate)
    (h : canWriteHolstNiehYanComponents g) :
    g.activeHolstNiehYanFLRWReduction \/ g.torsionlessRadialZeroIdentityReady := by
  exact h.right.right.left

theorem torsionless_radial_zero_identity_suffices_for_holst_components
    (g : HolstNiehYanComponentFromInputsGate)
    (hCore : g.activeCoreZ2Sigma)
    (hSource : g.activeDerivedSource)
    (hZero : g.torsionlessRadialZeroIdentityReady)
    (hGrid : g.aGridDeclared)
    (hProv : g.componentProvenanceChecked)
    (hPlanck : g.compressedPlanckLCDMForbidden)
    (hZ4 : g.archivedZ4ReuseForbidden)
    (hBAO : g.phenomenologicalHolstBAOScanForbidden) :
    canWriteHolstNiehYanComponents g := by
  exact ⟨hCore, hSource, Or.inr hZero, hGrid, hProv, hPlanck, hZ4, hBAO⟩

end P0EFTJanusZ2SigmaHolstNiehYanComponentFromInputsGate
end JanusFormal

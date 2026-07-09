namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermComponentFromInputsGate

set_option autoImplicit false

structure CountertermComponentFromInputsGate where
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  activeCountertermFLRWReduction : Prop
  countertermRadialReductionReady : Prop
  aGridDeclared : Prop
  componentProvenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  componentOutputWritten : Prop

def canWriteCountertermComponents
    (g : CountertermComponentFromInputsGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.activeCountertermFLRWReduction /\
  g.countertermRadialReductionReady /\
  g.aGridDeclared /\
  g.componentProvenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden

theorem counterterm_components_require_active_reduction
    (g : CountertermComponentFromInputsGate)
    (h : canWriteCountertermComponents g) :
    g.activeCountertermFLRWReduction := by
  exact h.2.2.1

theorem counterterm_components_require_radial_reduction
    (g : CountertermComponentFromInputsGate)
    (h : canWriteCountertermComponents g) :
    g.countertermRadialReductionReady := by
  exact h.2.2.2.1

end P0EFTJanusZ2SigmaCountertermComponentFromInputsGate
end JanusFormal

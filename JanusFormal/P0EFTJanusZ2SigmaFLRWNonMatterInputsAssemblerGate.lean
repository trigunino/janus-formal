namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWNonMatterInputsAssemblerGate

set_option autoImplicit false

structure FLRWNonMatterInputsAssemblerGate where
  cartanGHYComponentDeclared : Prop
  holstNiehYanComponentDeclared : Prop
  countertermComponentDeclared : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  aGridsAligned : Prop
  componentProvenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  cartanGHYComponentFrontierDeclared : Prop
  holstNiehYanComponentFrontierDeclared : Prop
  countertermComponentFrontierDeclared : Prop
  nearestNonMatterFrontierDeclared : Prop
  nearestNonMatterFrontierDiagnosticOnly : Prop
  nonMatterFLRWInputsWritten : Prop

def canAssembleNonMatterFLRWInputs
    (g : FLRWNonMatterInputsAssemblerGate) : Prop :=
  g.cartanGHYComponentDeclared /\
  g.holstNiehYanComponentDeclared /\
  g.countertermComponentDeclared /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.aGridsAligned /\
  g.componentProvenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.cartanGHYComponentFrontierDeclared /\
  g.holstNiehYanComponentFrontierDeclared /\
  g.countertermComponentFrontierDeclared /\
  g.nearestNonMatterFrontierDeclared /\
  g.nearestNonMatterFrontierDiagnosticOnly

theorem non_matter_assembly_requires_all_components
    (g : FLRWNonMatterInputsAssemblerGate)
    (h : canAssembleNonMatterFLRWInputs g) :
    g.cartanGHYComponentDeclared /\ g.holstNiehYanComponentDeclared /\ g.countertermComponentDeclared := by
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem non_matter_assembly_forbids_legacy_inputs
    (g : FLRWNonMatterInputsAssemblerGate)
    (h : canAssembleNonMatterFLRWInputs g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, hPlanck, hZ4, _⟩
  exact ⟨hPlanck, hZ4⟩

theorem non_matter_assembly_declares_component_frontiers
    (g : FLRWNonMatterInputsAssemblerGate)
    (h : canAssembleNonMatterFLRWInputs g) :
    g.cartanGHYComponentFrontierDeclared /\
    g.holstNiehYanComponentFrontierDeclared /\
    g.countertermComponentFrontierDeclared /\
    g.nearestNonMatterFrontierDeclared /\
    g.nearestNonMatterFrontierDiagnosticOnly := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hCartan, hHolst, hCounterterm, hFrontier, hDiag⟩
  exact ⟨hCartan, hHolst, hCounterterm, hFrontier, hDiag⟩

end P0EFTJanusZ2SigmaFLRWNonMatterInputsAssemblerGate
end JanusFormal

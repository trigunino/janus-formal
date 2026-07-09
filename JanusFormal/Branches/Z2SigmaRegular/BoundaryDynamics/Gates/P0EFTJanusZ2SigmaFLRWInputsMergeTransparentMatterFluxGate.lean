namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWInputsMergeTransparentMatterFluxGate

set_option autoImplicit false

structure FLRWInputsMergeTransparentMatterFluxGate where
  partialFLRWInputsDeclared : Prop
  transparentMatterFluxComponentDeclared : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  activeSigmaTransparencyDerived : Prop
  aGridAligned : Prop
  nonMatterFLRWComponentsDeclared : Prop
  matterFluxZeroComponentsDeclared : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  mergedFLRWComponentInputsWritten : Prop
  zeroMatterFluxComponentFrontierDeclared : Prop
  nearestMatterFluxMergeFrontierDeclared : Prop
  nearestMatterFluxMergeFrontierDiagnosticOnly : Prop

def canMergeTransparentMatterFluxIntoFLRWInputs
    (g : FLRWInputsMergeTransparentMatterFluxGate) : Prop :=
  g.partialFLRWInputsDeclared /\
  g.transparentMatterFluxComponentDeclared /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.activeSigmaTransparencyDerived /\
  g.aGridAligned /\
  g.nonMatterFLRWComponentsDeclared /\
  g.matterFluxZeroComponentsDeclared /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.zeroMatterFluxComponentFrontierDeclared /\
  g.nearestMatterFluxMergeFrontierDeclared /\
  g.nearestMatterFluxMergeFrontierDiagnosticOnly

theorem merge_requires_transparency
    (g : FLRWInputsMergeTransparentMatterFluxGate)
    (h : canMergeTransparentMatterFluxIntoFLRWInputs g) :
    g.activeSigmaTransparencyDerived := by
  exact h.2.2.2.2.1

theorem merge_forbids_legacy_inputs
    (g : FLRWInputsMergeTransparentMatterFluxGate)
    (h : canMergeTransparentMatterFluxIntoFLRWInputs g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hPlanck, hZ4, _, _, _, _⟩
  exact And.intro hPlanck hZ4

theorem nearest_matter_flux_merge_frontier_diagnostic_does_not_merge
    (g : FLRWInputsMergeTransparentMatterFluxGate)
    (_hDiag : g.nearestMatterFluxMergeFrontierDiagnosticOnly)
    (hNoMatterFlux : Not g.matterFluxZeroComponentsDeclared) :
    Not (g.nearestMatterFluxMergeFrontierDiagnosticOnly /\
      canMergeTransparentMatterFluxIntoFLRWInputs g) := by
  intro h
  rcases h.2 with ⟨_, _, _, _, _, _, _, hMatterFlux, _, _, _, _, _, _, _⟩
  exact hNoMatterFlux hMatterFlux

end P0EFTJanusZ2SigmaFLRWInputsMergeTransparentMatterFluxGate
end JanusFormal

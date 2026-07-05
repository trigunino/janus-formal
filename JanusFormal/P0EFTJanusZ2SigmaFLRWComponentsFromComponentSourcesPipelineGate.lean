namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWComponentsFromComponentSourcesPipelineGate

set_option autoImplicit false

structure FLRWComponentsFromComponentSourcesPipelineGate where
  activeCoreZ2TunnelSigma : Prop
  cartanGHYComponentsValid : Prop
  holstNiehYanComponentsValid : Prop
  countertermComponentsValid : Prop
  transparentMatterFluxComponentsValid : Prop
  nonMatterInputsPassed : Prop
  transparentMatterFluxMergePassed : Prop
  flrwComponentManifestWriterPassed : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  gatePassed : Prop
  nonMatterFrontierDeclared : Prop
  nonMatterSubFrontiersDeclared : Prop
  nearestNonMatterFrontierDeclared : Prop
  matterFluxMergeFrontierDeclared : Prop
  manifestWriterFrontierDeclared : Prop
  nearestFLRWComponentsFrontierDeclared : Prop
  nearestFLRWComponentsFrontierDiagnosticOnly : Prop

def noLegacyFLRWComponentInputs
    (g : FLRWComponentsFromComponentSourcesPipelineGate) : Prop :=
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed

def flrwComponentsReady
    (g : FLRWComponentsFromComponentSourcesPipelineGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.cartanGHYComponentsValid /\
  g.holstNiehYanComponentsValid /\
  g.countertermComponentsValid /\
  g.transparentMatterFluxComponentsValid /\
  g.nonMatterInputsPassed /\
  g.transparentMatterFluxMergePassed /\
  g.flrwComponentManifestWriterPassed /\
  noLegacyFLRWComponentInputs g /\
  g.nonMatterFrontierDeclared /\
  g.nonMatterSubFrontiersDeclared /\
  g.nearestNonMatterFrontierDeclared /\
  g.matterFluxMergeFrontierDeclared /\
  g.manifestWriterFrontierDeclared /\
  g.nearestFLRWComponentsFrontierDeclared /\
  g.nearestFLRWComponentsFrontierDiagnosticOnly

theorem gate_pass_requires_flrw_component_source_chain
    (g : FLRWComponentsFromComponentSourcesPipelineGate)
    (hPass : g.gatePassed)
    (hImplies : g.gatePassed -> flrwComponentsReady g) :
    flrwComponentsReady g := by
  exact hImplies hPass

theorem flrw_components_require_non_matter_inputs
    (g : FLRWComponentsFromComponentSourcesPipelineGate)
    (hReady : flrwComponentsReady g) :
    g.nonMatterInputsPassed := by
  rcases hReady with ⟨_, _, _, _, _, hNonMatter, _⟩
  exact hNonMatter

theorem nearest_flrw_frontier_diagnostic_does_not_close_components
    (g : FLRWComponentsFromComponentSourcesPipelineGate)
    (_hDiag : g.nearestFLRWComponentsFrontierDiagnosticOnly)
    (hNoNonMatter : Not g.nonMatterInputsPassed) :
    Not (g.nearestFLRWComponentsFrontierDiagnosticOnly /\ flrwComponentsReady g) := by
  intro h
  exact hNoNonMatter (flrw_components_require_non_matter_inputs g h.2)

theorem flrw_components_declare_non_matter_subfrontiers
    (g : FLRWComponentsFromComponentSourcesPipelineGate)
    (hReady : flrwComponentsReady g) :
    g.nonMatterSubFrontiersDeclared /\ g.nearestNonMatterFrontierDeclared := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, _, _, hSub, hNearest, _⟩
  exact ⟨hSub, hNearest⟩

end P0EFTJanusZ2SigmaFLRWComponentsFromComponentSourcesPipelineGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxZeroComponentFromTransparencyGate

set_option autoImplicit false

structure MatterFluxZeroComponentFromTransparencyGate where
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  activeSigmaTransparencyDerived : Prop
  aGridDeclared : Prop
  transparencyProvenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  zeroComponentOutputWritten : Prop
  transparencyInputWriterGateDeclared : Prop
  nearestZeroMatterFluxFrontierDeclared : Prop
  nearestZeroMatterFluxFrontierDiagnosticOnly : Prop

def canWriteZeroMatterFluxComponents
    (g : MatterFluxZeroComponentFromTransparencyGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.activeSigmaTransparencyDerived /\
  g.aGridDeclared /\
  g.transparencyProvenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.transparencyInputWriterGateDeclared /\
  g.nearestZeroMatterFluxFrontierDeclared /\
  g.nearestZeroMatterFluxFrontierDiagnosticOnly

theorem zero_flux_components_require_active_transparency
    (g : MatterFluxZeroComponentFromTransparencyGate)
    (h : canWriteZeroMatterFluxComponents g) :
    g.activeSigmaTransparencyDerived := by
  exact h.2.2.1

theorem zero_flux_components_forbid_legacy_inputs
    (g : MatterFluxZeroComponentFromTransparencyGate)
    (h : canWriteZeroMatterFluxComponents g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, _, _, _, hPlanck, hZ4, _, _, _, _⟩
  exact And.intro hPlanck hZ4

theorem nearest_zero_flux_frontier_diagnostic_does_not_write_components
    (g : MatterFluxZeroComponentFromTransparencyGate)
    (_hDiag : g.nearestZeroMatterFluxFrontierDiagnosticOnly)
    (hNoTransparency : Not g.activeSigmaTransparencyDerived) :
    Not (g.nearestZeroMatterFluxFrontierDiagnosticOnly /\
      canWriteZeroMatterFluxComponents g) := by
  intro h
  rcases h.2 with ⟨_, _, hTransparency, _, _, _, _, _, _, _, _⟩
  exact hNoTransparency hTransparency

end P0EFTJanusZ2SigmaMatterFluxZeroComponentFromTransparencyGate
end JanusFormal

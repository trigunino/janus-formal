namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxTransparencyInputWriterGate

set_option autoImplicit false

structure MatterFluxTransparencyInputWriterGate where
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  aGridDeclared : Prop
  noNormalMatterCurrentReady : Prop
  normalMatterCurrentGateReady : Prop
  bulkStressProjectionReady : Prop
  bulkStressCancellationReady : Prop
  bulkStressFluxZeroReady : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  transparencyInputWritten : Prop
  normalMatterCurrentFrontierDeclared : Prop
  bulkStressNormalFluxFrontierDeclared : Prop
  nearestTransparencyInputFrontierDeclared : Prop
  nearestTransparencyInputFrontierDiagnosticOnly : Prop

def canWriteMatterFluxTransparencyInput
    (g : MatterFluxTransparencyInputWriterGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.aGridDeclared /\
  g.noNormalMatterCurrentReady /\
  g.normalMatterCurrentGateReady /\
  g.bulkStressProjectionReady /\
  g.bulkStressCancellationReady /\
  g.bulkStressFluxZeroReady /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.normalMatterCurrentFrontierDeclared /\
  g.bulkStressNormalFluxFrontierDeclared /\
  g.nearestTransparencyInputFrontierDeclared /\
  g.nearestTransparencyInputFrontierDiagnosticOnly

theorem transparency_input_requires_current_and_flux_closure
    (g : MatterFluxTransparencyInputWriterGate)
    (h : canWriteMatterFluxTransparencyInput g) :
    g.noNormalMatterCurrentReady /\
    g.normalMatterCurrentGateReady /\
    g.bulkStressProjectionReady /\
    g.bulkStressCancellationReady /\
    g.bulkStressFluxZeroReady := by
  rcases h with ⟨_, _, _, hCurrent, hCurrentGate, hProjection, hCancel, hZero, _⟩
  exact ⟨hCurrent, hCurrentGate, hProjection, hCancel, hZero⟩

theorem transparency_input_forbids_legacy_inputs
    (g : MatterFluxTransparencyInputWriterGate)
    (h : canWriteMatterFluxTransparencyInput g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hPlanck, hZ4, _⟩
  exact ⟨hPlanck, hZ4⟩

theorem nearest_transparency_frontier_diagnostic_does_not_write_input
    (g : MatterFluxTransparencyInputWriterGate)
    (_hDiag : g.nearestTransparencyInputFrontierDiagnosticOnly)
    (hNoCurrent : Not g.noNormalMatterCurrentReady) :
    Not (g.nearestTransparencyInputFrontierDiagnosticOnly /\
      canWriteMatterFluxTransparencyInput g) := by
  intro h
  exact hNoCurrent (transparency_input_requires_current_and_flux_closure g h.2).1

end P0EFTJanusZ2SigmaMatterFluxTransparencyInputWriterGate
end JanusFormal

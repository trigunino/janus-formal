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
  perfectFluidFluxZeroReady : Prop
  holstBoundaryFluxZeroReady : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  transparencyInputWritten : Prop
  normalMatterCurrentFrontierDeclared : Prop
  bulkStressNormalFluxFrontierDeclared : Prop
  nearestTransparencyInputFrontierDeclared : Prop
  nearestTransparencyInputFrontierDiagnosticOnly : Prop

def fullBulkTransparencyReady
    (g : MatterFluxTransparencyInputWriterGate) : Prop :=
  g.noNormalMatterCurrentReady /\
  g.normalMatterCurrentGateReady /\
  g.bulkStressProjectionReady /\
  g.bulkStressCancellationReady /\
  g.bulkStressFluxZeroReady

def localSigmaFluxSlotReady
    (g : MatterFluxTransparencyInputWriterGate) : Prop :=
  g.perfectFluidFluxZeroReady /\ g.holstBoundaryFluxZeroReady

def canWriteMatterFluxTransparencyInput
    (g : MatterFluxTransparencyInputWriterGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.aGridDeclared /\
  (fullBulkTransparencyReady g \/ localSigmaFluxSlotReady g) /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.normalMatterCurrentFrontierDeclared /\
  g.bulkStressNormalFluxFrontierDeclared /\
  g.nearestTransparencyInputFrontierDeclared /\
  g.nearestTransparencyInputFrontierDiagnosticOnly

theorem transparency_input_requires_full_or_local_flux_closure
    (g : MatterFluxTransparencyInputWriterGate)
    (h : canWriteMatterFluxTransparencyInput g) :
    fullBulkTransparencyReady g \/ localSigmaFluxSlotReady g := by
  exact h.right.right.right.left

theorem local_sigma_flux_slot_suffices_for_transparency_input
    (g : MatterFluxTransparencyInputWriterGate)
    (hCore : g.activeCoreZ2Sigma)
    (hSource : g.activeDerivedSource)
    (hGrid : g.aGridDeclared)
    (hLocal : localSigmaFluxSlotReady g)
    (hPlanck : g.compressedPlanckLCDMForbidden)
    (hZ4 : g.archivedZ4ReuseForbidden)
    (hBAO : g.phenomenologicalHolstBAOScanForbidden)
    (hCurrentFrontier : g.normalMatterCurrentFrontierDeclared)
    (hBulkFrontier : g.bulkStressNormalFluxFrontierDeclared)
    (hNearest : g.nearestTransparencyInputFrontierDeclared)
    (hDiag : g.nearestTransparencyInputFrontierDiagnosticOnly) :
    canWriteMatterFluxTransparencyInput g := by
  exact ⟨hCore, hSource, hGrid, Or.inr hLocal, hPlanck, hZ4, hBAO,
    hCurrentFrontier, hBulkFrontier, hNearest, hDiag⟩

theorem transparency_input_forbids_legacy_inputs
    (g : MatterFluxTransparencyInputWriterGate)
    (h : canWriteMatterFluxTransparencyInput g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  exact ⟨h.right.right.right.right.left,
    h.right.right.right.right.right.left⟩

theorem missing_both_full_and_local_flux_closure_blocks_input
    (g : MatterFluxTransparencyInputWriterGate)
    (hNoFull : Not (fullBulkTransparencyReady g))
    (hNoLocal : Not (localSigmaFluxSlotReady g)) :
    Not (canWriteMatterFluxTransparencyInput g) := by
  intro h
  cases transparency_input_requires_full_or_local_flux_closure g h with
  | inl hFull => exact hNoFull hFull
  | inr hLocal => exact hNoLocal hLocal

end P0EFTJanusZ2SigmaMatterFluxTransparencyInputWriterGate
end JanusFormal

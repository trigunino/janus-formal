namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveInputsToOfficialBAOGate

set_option autoImplicit false

structure ActiveInputsToOfficialBAOGate where
  backgroundScalarInputValid : Prop
  flrwComponentInputValid : Prop
  earlyPlasmaInputValid : Prop
  countertermRadialReductionReady : Prop
  atomicPreflightPassed : Prop
  backgroundScalarManifestWritten : Prop
  flrwComponentManifestWritten : Prop
  earlyPlasmaManifestWritten : Prop
  baoComponentManifestWritten : Prop
  baoInputManifestWritten : Prop
  officialBAOEvaluation : Prop
  baoChi2Evaluated : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4Forbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop

def officialBAOPathReady (g : ActiveInputsToOfficialBAOGate) : Prop :=
  g.backgroundScalarInputValid /\
  g.flrwComponentInputValid /\
  g.earlyPlasmaInputValid /\
  g.countertermRadialReductionReady /\
  g.atomicPreflightPassed /\
  g.backgroundScalarManifestWritten /\
  g.flrwComponentManifestWritten /\
  g.earlyPlasmaManifestWritten /\
  g.baoComponentManifestWritten /\
  g.baoInputManifestWritten /\
  g.officialBAOEvaluation /\
  g.baoChi2Evaluated /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4Forbidden /\
  g.phenomenologicalHolstBAOScanForbidden

theorem missing_flrw_input_blocks_official_bao
    (g : ActiveInputsToOfficialBAOGate)
    (hMissing : Not g.flrwComponentInputValid) :
    Not (officialBAOPathReady g) := by
  intro h
  exact hMissing h.2.1

theorem official_bao_path_forbids_legacy_inputs
    (g : ActiveInputsToOfficialBAOGate)
    (h : officialBAOPathReady g) :
    g.compressedPlanckLCDMForbidden /\
      g.archivedZ4Forbidden /\
      g.phenomenologicalHolstBAOScanForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hNoPlanck, hNoZ4, hNoHolst⟩
  exact ⟨hNoPlanck, hNoZ4, hNoHolst⟩

theorem official_bao_path_requires_counterterm_reduction
    (g : ActiveInputsToOfficialBAOGate)
    (h : officialBAOPathReady g) :
    g.countertermRadialReductionReady := by
  rcases h with ⟨_, _, _, hCounterterm, _, _, _, _, _, _, _, _, _, _, _⟩
  exact hCounterterm

end P0EFTJanusZ2SigmaActiveInputsToOfficialBAOGate
end JanusFormal

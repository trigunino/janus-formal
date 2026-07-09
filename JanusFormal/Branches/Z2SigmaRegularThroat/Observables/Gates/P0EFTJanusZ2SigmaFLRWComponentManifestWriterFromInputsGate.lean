namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWComponentManifestWriterFromInputsGate

set_option autoImplicit false

structure FLRWComponentManifestWriterFromInputsGate where
  inputManifestDeclared : Prop
  inputManifestValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  aGridDeclared : Prop
  cartanGHYInputsDeclared : Prop
  holstNiehYanInputsDeclared : Prop
  matterFluxInputsDeclared : Prop
  countertermInputsDeclared : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  manifestWritten : Prop

def canWriteOfficialFLRWComponentManifest
    (g : FLRWComponentManifestWriterFromInputsGate) : Prop :=
  g.inputManifestDeclared /\
  g.inputManifestValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.aGridDeclared /\
  g.cartanGHYInputsDeclared /\
  g.holstNiehYanInputsDeclared /\
  g.matterFluxInputsDeclared /\
  g.countertermInputsDeclared /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden

theorem missing_input_blocks_official_write
    (g : FLRWComponentManifestWriterFromInputsGate)
    (hMissing : Not g.inputManifestValid) :
    Not (canWriteOfficialFLRWComponentManifest g) := by
  intro h
  exact hMissing h.2.1

theorem official_write_forbids_legacy_inputs
    (g : FLRWComponentManifestWriterFromInputsGate)
    (h : canWriteOfficialFLRWComponentManifest g) :
    g.compressedPlanckLCDMForbidden /\
      g.archivedZ4ReuseForbidden /\
      g.phenomenologicalHolstBAOScanForbidden := by
  exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

end P0EFTJanusZ2SigmaFLRWComponentManifestWriterFromInputsGate
end JanusFormal


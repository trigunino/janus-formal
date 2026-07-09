namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaManifestWriterFromInputsGate

set_option autoImplicit false

structure EarlyPlasmaManifestWriterFromInputsGate where
  inputManifestDeclared : Prop
  inputManifestValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  baryonPhotonNormalizationsDeclared : Prop
  ionizationAndThomsonInputsDeclared : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  manifestWritten : Prop

def canWriteOfficialEarlyPlasmaManifest
    (g : EarlyPlasmaManifestWriterFromInputsGate) : Prop :=
  g.inputManifestDeclared /\
  g.inputManifestValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.baryonPhotonNormalizationsDeclared /\
  g.ionizationAndThomsonInputsDeclared /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden

theorem missing_input_blocks_official_write
    (g : EarlyPlasmaManifestWriterFromInputsGate)
    (hMissing : Not g.inputManifestValid) :
    Not (canWriteOfficialEarlyPlasmaManifest g) := by
  intro h
  exact hMissing h.2.1

theorem official_write_requires_noncompressed_inputs
    (g : EarlyPlasmaManifestWriterFromInputsGate)
    (h : canWriteOfficialEarlyPlasmaManifest g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end P0EFTJanusZ2SigmaEarlyPlasmaManifestWriterFromInputsGate
end JanusFormal


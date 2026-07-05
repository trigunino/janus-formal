namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundScalarManifestWriterFromInputsGate

set_option autoImplicit false

structure BackgroundScalarManifestWriterFromInputsGate where
  inputManifestDeclared : Prop
  inputManifestValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  H0InputDeclared : Prop
  omegaKInputDeclared : Prop
  GConventionInputDeclared : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  observationalH0FitForbidden : Prop
  manifestWritten : Prop

def canWriteOfficialBackgroundScalarManifest
    (g : BackgroundScalarManifestWriterFromInputsGate) : Prop :=
  g.inputManifestDeclared /\
  g.inputManifestValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.H0InputDeclared /\
  g.omegaKInputDeclared /\
  g.GConventionInputDeclared /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.observationalH0FitForbidden

theorem missing_input_blocks_official_write
    (g : BackgroundScalarManifestWriterFromInputsGate)
    (hMissing : Not g.inputManifestValid) :
    Not (canWriteOfficialBackgroundScalarManifest g) := by
  intro h
  exact hMissing h.2.1

theorem official_write_forbids_compressed_background
    (g : BackgroundScalarManifestWriterFromInputsGate)
    (h : canWriteOfficialBackgroundScalarManifest g) :
    g.compressedPlanckLCDMForbidden /\
      g.archivedZ4ReuseForbidden /\
      g.observationalH0FitForbidden := by
  exact ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

end P0EFTJanusZ2SigmaBackgroundScalarManifestWriterFromInputsGate
end JanusFormal


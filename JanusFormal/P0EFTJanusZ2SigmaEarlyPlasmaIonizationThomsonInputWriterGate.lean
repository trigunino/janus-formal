namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaIonizationThomsonInputWriterGate

set_option autoImplicit false

structure IonizationThomsonInputWriterGate where
  normalizationInputDeclared : Prop
  normalizationInputValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  zGridDeclared : Prop
  ionizationFractionDeclared : Prop
  electronsPerBaryonDeclared : Prop
  sigmaThomsonDeclared : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  outputWritten : Prop

def canWriteIonizationThomsonInput (g : IonizationThomsonInputWriterGate) : Prop :=
  g.normalizationInputDeclared /\
  g.normalizationInputValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.zGridDeclared /\
  g.ionizationFractionDeclared /\
  g.electronsPerBaryonDeclared /\
  g.sigmaThomsonDeclared /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden

theorem invalid_input_blocks_ionization_thomson_write
    (g : IonizationThomsonInputWriterGate)
    (hInvalid : Not g.normalizationInputValid) :
    Not (canWriteIonizationThomsonInput g) := by
  intro h
  exact hInvalid h.2.1

theorem ionization_thomson_write_requires_active_provenance
    (g : IonizationThomsonInputWriterGate)
    (h : canWriteIonizationThomsonInput g) :
    g.activeCoreZ2Sigma /\ g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, hCore, _, _, _, _, _, _, hPlanck, hZ4⟩
  exact ⟨hCore, hPlanck, hZ4⟩

end P0EFTJanusZ2SigmaEarlyPlasmaIonizationThomsonInputWriterGate
end JanusFormal

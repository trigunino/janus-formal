namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaBaryonPhotonInputWriterGate

set_option autoImplicit false

structure BaryonPhotonInputWriterGate where
  normalizationInputDeclared : Prop
  normalizationInputValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  zGridDeclared : Prop
  rhoBaryon0Declared : Prop
  photonTemperature0Declared : Prop
  radiationConstantDeclared : Prop
  baryonMassConventionDeclared : Prop
  baryonNumberDensityDeclared : Prop
  baryonMassDensityConsistent : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  outputWritten : Prop

def canWriteBaryonPhotonInput (g : BaryonPhotonInputWriterGate) : Prop :=
  g.normalizationInputDeclared /\
  g.normalizationInputValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.zGridDeclared /\
  g.rhoBaryon0Declared /\
  g.photonTemperature0Declared /\
  g.radiationConstantDeclared /\
  g.baryonMassConventionDeclared /\
  g.baryonNumberDensityDeclared /\
  g.baryonMassDensityConsistent /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden

theorem invalid_input_blocks_baryon_photon_write
    (g : BaryonPhotonInputWriterGate)
    (hInvalid : Not g.normalizationInputValid) :
    Not (canWriteBaryonPhotonInput g) := by
  intro h
  exact hInvalid h.2.1

theorem baryon_photon_write_requires_active_provenance
    (g : BaryonPhotonInputWriterGate)
    (h : canWriteBaryonPhotonInput g) :
    g.activeCoreZ2Sigma /\ g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, hCore, _, _, _, _, _, _, _, _, _, hPlanck, hZ4⟩
  exact ⟨hCore, hPlanck, hZ4⟩

end P0EFTJanusZ2SigmaEarlyPlasmaBaryonPhotonInputWriterGate
end JanusFormal

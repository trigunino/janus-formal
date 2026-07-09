namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaInputsAssemblerGate

set_option autoImplicit false

structure EarlyPlasmaInputsAssemblerGate where
  baryonPhotonInputDeclared : Prop
  baryonPhotonInputValid : Prop
  ionizationThomsonInputDeclared : Prop
  ionizationThomsonInputValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  zGridAligned : Prop
  baryonMassDensityConsistent : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  assembledInputWritten : Prop

def canAssembleEarlyPlasmaInputs
    (g : EarlyPlasmaInputsAssemblerGate) : Prop :=
  g.baryonPhotonInputDeclared /\
  g.baryonPhotonInputValid /\
  g.ionizationThomsonInputDeclared /\
  g.ionizationThomsonInputValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.zGridAligned /\
  g.baryonMassDensityConsistent /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden

theorem missing_baryon_photon_input_blocks_assembly
    (g : EarlyPlasmaInputsAssemblerGate)
    (hMissing : Not g.baryonPhotonInputValid) :
    Not (canAssembleEarlyPlasmaInputs g) := by
  intro h
  exact hMissing h.2.1

theorem missing_ionization_thomson_input_blocks_assembly
    (g : EarlyPlasmaInputsAssemblerGate)
    (hMissing : Not g.ionizationThomsonInputValid) :
    Not (canAssembleEarlyPlasmaInputs g) := by
  intro h
  exact hMissing h.2.2.2.1

theorem assembly_requires_active_noncompressed_provenance
    (g : EarlyPlasmaInputsAssemblerGate)
    (h : canAssembleEarlyPlasmaInputs g) :
    g.activeCoreZ2Sigma /\ g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  exact And.intro h.2.2.2.2.1
    (And.intro h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2)

end P0EFTJanusZ2SigmaEarlyPlasmaInputsAssemblerGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaComponentManifestGate

set_option autoImplicit false

structure EarlyPlasmaComponentManifestGate where
  writerReady : Prop
  loaderValidationReady : Prop
  rhoBaryonFieldDeclared : Prop
  rhoPhotonFieldDeclared : Prop
  gammaDragFieldDeclared : Prop
  requiresActiveProvenance : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  earlyPlasmaValuesReady : Prop

def strictEarlyPlasmaManifestReady
    (g : EarlyPlasmaComponentManifestGate) : Prop :=
  g.writerReady /\
  g.loaderValidationReady /\
  g.rhoBaryonFieldDeclared /\
  g.rhoPhotonFieldDeclared /\
  g.gammaDragFieldDeclared /\
  g.requiresActiveProvenance /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden

theorem manifest_writer_does_not_supply_values
    (g : EarlyPlasmaComponentManifestGate)
    (_h : strictEarlyPlasmaManifestReady g)
    (hv : Not g.earlyPlasmaValuesReady) :
    Not g.earlyPlasmaValuesReady := by
  exact hv

end P0EFTJanusZ2SigmaEarlyPlasmaComponentManifestGate
end JanusFormal

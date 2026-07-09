namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaPhotonTemperatureFIRASGate

set_option autoImplicit false

structure EarlyPlasmaPhotonTemperatureFIRASGate where
  activeCoreZ2TunnelSigma : Prop
  firasReferenceChecked : Prop
  photonTemperatureDeclared : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  observationalFitUsed : Prop
  baryonOrIonizationNormalizationsFixed : Prop
  outputManifestWritten : Prop
  gatePassed : Prop

def directTemperaturePolicyClosed
    (g : EarlyPlasmaPhotonTemperatureFIRASGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.firasReferenceChecked /\
  g.photonTemperatureDeclared /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed /\
  Not g.observationalFitUsed /\
  Not g.baryonOrIonizationNormalizationsFixed

theorem gate_requires_written_temperature_manifest
    (g : EarlyPlasmaPhotonTemperatureFIRASGate)
    (hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.outputManifestWritten) :
    g.outputManifestWritten := by
  exact hImplies hGate

theorem firas_temperature_does_not_fix_baryon_or_ionization
    (g : EarlyPlasmaPhotonTemperatureFIRASGate)
    (hPolicy : directTemperaturePolicyClosed g) :
    Not g.baryonOrIonizationNormalizationsFixed := by
  exact hPolicy.right.right.right.right.right.right.right

end P0EFTJanusZ2SigmaEarlyPlasmaPhotonTemperatureFIRASGate
end JanusFormal

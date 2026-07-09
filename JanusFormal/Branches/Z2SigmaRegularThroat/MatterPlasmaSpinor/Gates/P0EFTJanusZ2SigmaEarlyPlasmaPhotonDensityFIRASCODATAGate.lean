namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaPhotonDensityFIRASCODATAGate

set_option autoImplicit false

structure EarlyPlasmaPhotonDensityFIRASCODATAGate where
  activeCoreZ2TunnelSigma : Prop
  codataConstantsValid : Prop
  firasTemperatureValid : Prop
  rhoPhoton0Declared : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  observationalFitUsed : Prop
  baryonOrIonizationNormalizationsFixed : Prop
  gatePassed : Prop

def photonDensityPolicyClosed
    (g : EarlyPlasmaPhotonDensityFIRASCODATAGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.codataConstantsValid /\
  g.firasTemperatureValid /\
  g.rhoPhoton0Declared /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed /\
  Not g.observationalFitUsed /\
  Not g.baryonOrIonizationNormalizationsFixed

theorem photon_density_gate_requires_upstream_inputs
    (g : EarlyPlasmaPhotonDensityFIRASCODATAGate)
    (hGate : g.gatePassed)
    (hImplies :
      g.gatePassed -> g.codataConstantsValid /\ g.firasTemperatureValid) :
    g.codataConstantsValid /\ g.firasTemperatureValid := by
  exact hImplies hGate

end P0EFTJanusZ2SigmaEarlyPlasmaPhotonDensityFIRASCODATAGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaPhotonDensityHistoryFIRASCODATAGate

set_option autoImplicit false

structure PhotonDensityHistoryFIRASCODATAGate where
  activeCoreZ2TunnelSigma : Prop
  rhoPhoton0InputValid : Prop
  conservedPhotonScalingDeclared : Prop
  rhoPhotonHistoryAvailable : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  observationalFitUsed : Prop
  baryonOrIonizationNormalizationsFixed : Prop
  gatePassed : Prop

def photonHistoryPolicyClosed
    (g : PhotonDensityHistoryFIRASCODATAGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.rhoPhoton0InputValid /\
  g.conservedPhotonScalingDeclared /\
  g.rhoPhotonHistoryAvailable /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed /\
  Not g.observationalFitUsed /\
  Not g.baryonOrIonizationNormalizationsFixed

theorem photon_history_gate_requires_rho0
    (g : PhotonDensityHistoryFIRASCODATAGate)
    (hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.rhoPhoton0InputValid) :
    g.rhoPhoton0InputValid := by
  exact hImplies hGate

end P0EFTJanusZ2SigmaEarlyPlasmaPhotonDensityHistoryFIRASCODATAGate
end JanusFormal

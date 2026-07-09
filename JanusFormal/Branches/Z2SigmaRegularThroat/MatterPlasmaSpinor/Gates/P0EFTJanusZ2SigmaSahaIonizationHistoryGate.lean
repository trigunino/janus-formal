namespace JanusFormal
namespace P0EFTJanusZ2SigmaSahaIonizationHistoryGate

set_option autoImplicit false

structure SahaIonizationHistoryGate where
  activeCoreZ2TunnelSigma : Prop
  sahaHistoryFormulaDeclared : Prop
  baryonNumberInputValid : Prop
  photonTemperatureInputValid : Prop
  codataConstantsValid : Prop
  baryonNumberDensityFrontierDeclared : Prop
  photonTemperatureFIRASFrontierDeclared : Prop
  codataConstantsFrontierDeclared : Prop
  nearestSahaHistoryFrontierDeclared : Prop
  nearestSahaHistoryFrontierDiagnosticOnly : Prop
  planckLCDMRecombinationHistoryUsed : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  valuesReady : Prop
  gatePassed : Prop

def noLegacyIonizationHistoryInputs
    (g : SahaIonizationHistoryGate) : Prop :=
  Not g.planckLCDMRecombinationHistoryUsed /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed

def activeSahaHistoryReady
    (g : SahaIonizationHistoryGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.sahaHistoryFormulaDeclared /\
  g.baryonNumberInputValid /\
  g.photonTemperatureInputValid /\
  g.codataConstantsValid /\
  g.baryonNumberDensityFrontierDeclared /\
  g.photonTemperatureFIRASFrontierDeclared /\
  g.codataConstantsFrontierDeclared /\
  g.nearestSahaHistoryFrontierDeclared /\
  g.nearestSahaHistoryFrontierDiagnosticOnly /\
  noLegacyIonizationHistoryInputs g

theorem saha_history_values_require_active_inputs
    (g : SahaIonizationHistoryGate)
    (hValues : g.valuesReady)
    (hImplies :
      g.valuesReady ->
        g.baryonNumberInputValid /\
        g.photonTemperatureInputValid /\
        g.codataConstantsValid) :
    g.baryonNumberInputValid /\
    g.photonTemperatureInputValid /\
    g.codataConstantsValid := by
  exact hImplies hValues

theorem gate_pass_requires_active_saha_history
    (g : SahaIonizationHistoryGate)
    (hPass : g.gatePassed)
    (hImplies : g.gatePassed -> activeSahaHistoryReady g) :
    activeSahaHistoryReady g := by
  exact hImplies hPass

theorem gate_forbids_legacy_ionization_history_inputs
    (g : SahaIonizationHistoryGate)
    (hPolicy : noLegacyIonizationHistoryInputs g) :
    Not g.planckLCDMRecombinationHistoryUsed /\
    Not g.compressedPlanckLCDMRdUsed /\
    Not g.archivedZ4InputsUsed /\
    Not g.phenomenologicalHolstBAOScanUsed := by
  exact hPolicy

theorem diagnostic_saha_frontier_does_not_supply_history
    (g : SahaIonizationHistoryGate)
    (_hDiag : g.nearestSahaHistoryFrontierDiagnosticOnly)
    (hNoBaryon : Not g.baryonNumberInputValid) :
    Not (g.nearestSahaHistoryFrontierDiagnosticOnly /\ activeSahaHistoryReady g) := by
  intro h
  exact hNoBaryon h.2.2.2.1

end P0EFTJanusZ2SigmaSahaIonizationHistoryGate
end JanusFormal

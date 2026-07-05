namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaSahaIonizationReadinessGate

set_option autoImplicit false

structure SahaIonizationReadinessGate where
  activeCoreZ2TunnelSigma : Prop
  primarySourcesChecked : Prop
  sahaFormulaDeclared : Prop
  photonTemperatureInputValid : Prop
  activeBaryonNumberInputValid : Prop
  planckLCDMRecombinationHistoryUsed : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  valuesReady : Prop
  gatePassed : Prop

def noLegacyIonizationInputs
    (g : SahaIonizationReadinessGate) : Prop :=
  Not g.planckLCDMRecombinationHistoryUsed /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed

theorem saha_values_require_baryon_number_and_temperature
    (g : SahaIonizationReadinessGate)
    (hValues : g.valuesReady)
    (hImplies :
      g.valuesReady -> g.photonTemperatureInputValid /\ g.activeBaryonNumberInputValid) :
    g.photonTemperatureInputValid /\ g.activeBaryonNumberInputValid := by
  exact hImplies hValues

theorem gate_forbids_legacy_recombination_inputs
    (g : SahaIonizationReadinessGate)
    (hPolicy : noLegacyIonizationInputs g) :
    Not g.planckLCDMRecombinationHistoryUsed /\
    Not g.compressedPlanckLCDMRdUsed /\
    Not g.archivedZ4InputsUsed /\
    Not g.phenomenologicalHolstBAOScanUsed := by
  exact hPolicy

end P0EFTJanusZ2SigmaEarlyPlasmaSahaIonizationReadinessGate
end JanusFormal

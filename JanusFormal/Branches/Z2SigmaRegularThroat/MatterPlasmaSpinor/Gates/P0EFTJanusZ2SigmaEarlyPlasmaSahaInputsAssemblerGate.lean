namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaSahaInputsAssemblerGate

set_option autoImplicit false

structure EarlyPlasmaSahaInputsAssemblerGate where
  activeCoreZ2TunnelSigma : Prop
  codataConstantsValid : Prop
  firasTemperatureValid : Prop
  sahaIonizationHistoryValid : Prop
  planckLCDMRecombinationHistoryUsed : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  earlyPlasmaInputsWritten : Prop
  gatePassed : Prop

def noLegacySahaAssemblerInputs
    (g : EarlyPlasmaSahaInputsAssemblerGate) : Prop :=
  Not g.planckLCDMRecombinationHistoryUsed /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed

def canAssembleSahaEarlyPlasmaInputs
    (g : EarlyPlasmaSahaInputsAssemblerGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.codataConstantsValid /\
  g.firasTemperatureValid /\
  g.sahaIonizationHistoryValid /\
  noLegacySahaAssemblerInputs g

theorem gate_pass_requires_saha_inputs
    (g : EarlyPlasmaSahaInputsAssemblerGate)
    (hPass : g.gatePassed)
    (hImplies : g.gatePassed -> canAssembleSahaEarlyPlasmaInputs g) :
    canAssembleSahaEarlyPlasmaInputs g := by
  exact hImplies hPass

theorem gate_forbids_legacy_saha_assembler_inputs
    (g : EarlyPlasmaSahaInputsAssemblerGate)
    (hPolicy : noLegacySahaAssemblerInputs g) :
    Not g.planckLCDMRecombinationHistoryUsed /\
    Not g.compressedPlanckLCDMRdUsed /\
    Not g.archivedZ4InputsUsed /\
    Not g.phenomenologicalHolstBAOScanUsed := by
  exact hPolicy

end P0EFTJanusZ2SigmaEarlyPlasmaSahaInputsAssemblerGate
end JanusFormal

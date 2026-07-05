namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaModelNormalizationAssemblerGate

set_option autoImplicit false

structure EarlyPlasmaModelNormalizationAssemblerGate where
  activeCoreZ2TunnelSigma : Prop
  codataConstantsManifestValid : Prop
  modelNormalizationManifestValid : Prop
  baryonPhotonSplitInputWritten : Prop
  ionizationThomsonSplitInputWritten : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  gatePassed : Prop

def splitInputsWritten
    (g : EarlyPlasmaModelNormalizationAssemblerGate) : Prop :=
  g.baryonPhotonSplitInputWritten /\ g.ionizationThomsonSplitInputWritten

def noLegacyNormalizationInputs
    (g : EarlyPlasmaModelNormalizationAssemblerGate) : Prop :=
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed

theorem gate_requires_constants_and_model_normalizations
    (g : EarlyPlasmaModelNormalizationAssemblerGate)
    (hGate : g.gatePassed)
    (hImplies :
      g.gatePassed ->
        g.codataConstantsManifestValid /\
        g.modelNormalizationManifestValid /\
        splitInputsWritten g) :
    g.codataConstantsManifestValid /\
    g.modelNormalizationManifestValid /\
    splitInputsWritten g := by
  exact hImplies hGate

theorem assembler_forbids_legacy_inputs
    (g : EarlyPlasmaModelNormalizationAssemblerGate)
    (hPolicy : noLegacyNormalizationInputs g) :
    Not g.compressedPlanckLCDMRdUsed /\
    Not g.archivedZ4InputsUsed /\
    Not g.phenomenologicalHolstBAOScanUsed := by
  exact hPolicy

end P0EFTJanusZ2SigmaEarlyPlasmaModelNormalizationAssemblerGate
end JanusFormal

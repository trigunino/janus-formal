namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaCODATAConstantsGate

set_option autoImplicit false

structure EarlyPlasmaCODATAConstantsGate where
  activeCoreZ2TunnelSigma : Prop
  codataNISTReferencesChecked : Prop
  radiationConstantDeclared : Prop
  baryonMassConventionDeclared : Prop
  thomsonCrossSectionDeclared : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  modelNormalizationsFixed : Prop
  outputManifestWritten : Prop
  gatePassed : Prop

def constantsPolicyClosed
    (g : EarlyPlasmaCODATAConstantsGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.codataNISTReferencesChecked /\
  g.radiationConstantDeclared /\
  g.baryonMassConventionDeclared /\
  g.thomsonCrossSectionDeclared /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.phenomenologicalHolstBAOScanUsed /\
  Not g.modelNormalizationsFixed

theorem gate_requires_written_constants_manifest
    (g : EarlyPlasmaCODATAConstantsGate)
    (hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.outputManifestWritten) :
    g.outputManifestWritten := by
  exact hImplies hGate

theorem constants_do_not_close_model_normalizations
    (g : EarlyPlasmaCODATAConstantsGate)
    (hPolicy : constantsPolicyClosed g) :
    Not g.modelNormalizationsFixed := by
  exact hPolicy.right.right.right.right.right.right.right.right

end P0EFTJanusZ2SigmaEarlyPlasmaCODATAConstantsGate
end JanusFormal

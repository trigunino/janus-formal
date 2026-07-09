namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundGravityCODATAConventionGate

set_option autoImplicit false

structure BackgroundGravityCODATAConventionGate where
  activeCoreZ2TunnelSigma : Prop
  codataNISTReferenceChecked : Prop
  gZ2SigmaSIConventionDeclared : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  cosmologicalParameterFitUsed : Prop
  outputManifestWritten : Prop
  gatePassed : Prop

def conventionPolicyClosed
    (g : BackgroundGravityCODATAConventionGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.codataNISTReferenceChecked /\
  g.gZ2SigmaSIConventionDeclared /\
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.cosmologicalParameterFitUsed

theorem gate_requires_written_convention_manifest
    (g : BackgroundGravityCODATAConventionGate)
    (hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.outputManifestWritten) :
    g.outputManifestWritten := by
  exact hImplies hGate

theorem convention_forbids_cosmology_fit_inputs
    (g : BackgroundGravityCODATAConventionGate)
    (hPolicy : conventionPolicyClosed g) :
    Not g.compressedPlanckLCDMBackgroundUsed /\
    Not g.archivedZ4BackgroundUsed /\
    Not g.observationalH0FitUsed /\
    Not g.cosmologicalParameterFitUsed := by
  rcases hPolicy with ⟨_, _, _, hNoPlanck, hNoZ4, hNoH0, hNoFit⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0, hNoFit⟩

end P0EFTJanusZ2SigmaBackgroundGravityCODATAConventionGate
end JanusFormal

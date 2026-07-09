namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundScalarInputsAssemblerGate

set_option autoImplicit false

structure BackgroundScalarInputsAssemblerGate where
  H0InputDeclared : Prop
  H0InputValid : Prop
  curvatureInputDeclared : Prop
  curvatureInputValid : Prop
  gravityInputDeclared : Prop
  gravityInputValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  observationalH0FitForbidden : Prop
  assembledInputWritten : Prop

def canAssembleBackgroundScalarInputs
    (g : BackgroundScalarInputsAssemblerGate) : Prop :=
  g.H0InputDeclared /\
  g.H0InputValid /\
  g.curvatureInputDeclared /\
  g.curvatureInputValid /\
  g.gravityInputDeclared /\
  g.gravityInputValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.observationalH0FitForbidden

theorem invalid_H0_blocks_background_scalar_assembly
    (g : BackgroundScalarInputsAssemblerGate)
    (hInvalid : Not g.H0InputValid) :
    Not (canAssembleBackgroundScalarInputs g) := by
  intro h
  exact hInvalid h.2.1

theorem background_scalar_assembly_forbids_compressed_inputs
    (g : BackgroundScalarInputsAssemblerGate)
    (h : canAssembleBackgroundScalarInputs g) :
    g.compressedPlanckLCDMForbidden /\
      g.archivedZ4ReuseForbidden /\
      g.observationalH0FitForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hPlanck, hZ4, hH0Fit⟩
  exact ⟨hPlanck, hZ4, hH0Fit⟩

end P0EFTJanusZ2SigmaBackgroundScalarInputsAssemblerGate
end JanusFormal

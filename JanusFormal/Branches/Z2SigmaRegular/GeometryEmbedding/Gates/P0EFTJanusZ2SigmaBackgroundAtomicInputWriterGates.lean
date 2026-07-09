namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundAtomicInputWriterGates

set_option autoImplicit false

structure BackgroundAtomicInputWriterGates where
  H0WriterDeclared : Prop
  H0InputValid : Prop
  requiresActiveH0ScaleNormalization : Prop
  dimensionlessH0ROverCInsufficientForH0 : Prop
  curvatureWriterDeclared : Prop
  projectiveTunnelTwoFoldTopologyReady : Prop
  topologyAloneFixesNumericOmegaK : Prop
  requiresActiveFLRWCurvatureRadiusOrEmbeddingScale : Prop
  curvatureInputValid : Prop
  gravityWriterDeclared : Prop
  gravityInputValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  observationalH0FitForbidden : Prop

def canWriteAllBackgroundAtomicInputs
    (g : BackgroundAtomicInputWriterGates) : Prop :=
  g.H0WriterDeclared /\
  g.H0InputValid /\
  g.requiresActiveH0ScaleNormalization /\
  g.dimensionlessH0ROverCInsufficientForH0 /\
  g.curvatureWriterDeclared /\
  g.projectiveTunnelTwoFoldTopologyReady /\
  Not g.topologyAloneFixesNumericOmegaK /\
  g.requiresActiveFLRWCurvatureRadiusOrEmbeddingScale /\
  g.curvatureInputValid /\
  g.gravityWriterDeclared /\
  g.gravityInputValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.observationalH0FitForbidden

theorem invalid_H0_blocks_atomic_background_writes
    (g : BackgroundAtomicInputWriterGates)
    (hInvalid : Not g.H0InputValid) :
    Not (canWriteAllBackgroundAtomicInputs g) := by
  intro h
  exact hInvalid h.2.1

theorem dimensional_H0_requires_active_scale_normalization
    (g : BackgroundAtomicInputWriterGates)
    (h : canWriteAllBackgroundAtomicInputs g) :
    g.requiresActiveH0ScaleNormalization /\
      g.dimensionlessH0ROverCInsufficientForH0 := by
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem topology_cover_alone_does_not_supply_numeric_omega_k
    (g : BackgroundAtomicInputWriterGates)
    (h : canWriteAllBackgroundAtomicInputs g) :
    Not g.topologyAloneFixesNumericOmegaK := by
  exact h.2.2.2.2.2.2.1

theorem atomic_background_writes_forbid_legacy_background
    (g : BackgroundAtomicInputWriterGates)
    (h : canWriteAllBackgroundAtomicInputs g) :
    g.compressedPlanckLCDMForbidden /\
      g.archivedZ4ReuseForbidden /\
      g.observationalH0FitForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hPlanck, hZ4, hH0Fit⟩
  exact ⟨hPlanck, hZ4, hH0Fit⟩

end P0EFTJanusZ2SigmaBackgroundAtomicInputWriterGates
end JanusFormal

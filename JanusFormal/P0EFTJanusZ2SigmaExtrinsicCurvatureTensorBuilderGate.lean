namespace JanusFormal
namespace P0EFTJanusZ2SigmaExtrinsicCurvatureTensorBuilderGate

set_option autoImplicit false

structure ExtrinsicCurvatureTensorBuilderGate where
  extrinsicCurvatureTensorBuilderReady : Prop
  flrwReductionReady : Prop
  requiresActiveEmbeddingSecondDerivatives : Prop
  requiresActiveChristoffelSymbols : Prop
  requiresActiveNormalCovector : Prop
  requiresActiveSpatialInverseMetric : Prop
  usesPlanckLCDMInputs : Prop
  usesArchivedZ4Inputs : Prop
  kAbValuesReady : Prop

def strictExtrinsicCurvatureTensorBuilderReady
    (g : ExtrinsicCurvatureTensorBuilderGate) : Prop :=
  g.extrinsicCurvatureTensorBuilderReady /\
  g.flrwReductionReady /\
  g.requiresActiveEmbeddingSecondDerivatives /\
  g.requiresActiveChristoffelSymbols /\
  g.requiresActiveNormalCovector /\
  g.requiresActiveSpatialInverseMetric /\
  ¬ g.usesPlanckLCDMInputs /\
  ¬ g.usesArchivedZ4Inputs

theorem k_ab_values_require_active_geometry
    (g : ExtrinsicCurvatureTensorBuilderGate)
    (hValues : g.kAbValuesReady)
    (hImplies :
      g.kAbValuesReady ->
        g.requiresActiveEmbeddingSecondDerivatives /\
        g.requiresActiveChristoffelSymbols /\
        g.requiresActiveNormalCovector) :
    g.requiresActiveEmbeddingSecondDerivatives /\
    g.requiresActiveChristoffelSymbols /\
    g.requiresActiveNormalCovector := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaExtrinsicCurvatureTensorBuilderGate
end JanusFormal

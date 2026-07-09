namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWExtrinsicCurvatureGridBuilderGate

set_option autoImplicit false

structure FLRWExtrinsicCurvatureGridBuilderGate where
  flrwKGridBuilderReady : Prop
  composesMetricGeometryPrimitives : Prop
  composesExtrinsicCurvatureTensorBuilder : Prop
  producesKsOfAArray : Prop
  producesKtauOfAArray : Prop
  requiresActiveAGrid : Prop
  requiresActiveTangentVectors : Prop
  requiresActiveSecondEmbedding : Prop
  requiresActiveChristoffelSymbols : Prop
  requiresActiveNormalCovector : Prop
  requiresActiveSpatialInverseMetric : Prop
  usesPlanckLCDMInputs : Prop
  usesArchivedZ4Inputs : Prop
  kSTauValuesReady : Prop

def strictFLRWKGridBuilderReady
    (g : FLRWExtrinsicCurvatureGridBuilderGate) : Prop :=
  g.flrwKGridBuilderReady /\
  g.composesMetricGeometryPrimitives /\
  g.composesExtrinsicCurvatureTensorBuilder /\
  g.producesKsOfAArray /\
  g.producesKtauOfAArray /\
  g.requiresActiveAGrid /\
  g.requiresActiveTangentVectors /\
  g.requiresActiveSecondEmbedding /\
  g.requiresActiveChristoffelSymbols /\
  g.requiresActiveNormalCovector /\
  g.requiresActiveSpatialInverseMetric /\
  ¬ g.usesPlanckLCDMInputs /\
  ¬ g.usesArchivedZ4Inputs

theorem k_grid_values_require_active_embedding_data
    (g : FLRWExtrinsicCurvatureGridBuilderGate)
    (hValues : g.kSTauValuesReady)
    (hImplies :
      g.kSTauValuesReady ->
        g.requiresActiveTangentVectors /\ g.requiresActiveSecondEmbedding) :
    g.requiresActiveTangentVectors /\ g.requiresActiveSecondEmbedding := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaFLRWExtrinsicCurvatureGridBuilderGate
end JanusFormal

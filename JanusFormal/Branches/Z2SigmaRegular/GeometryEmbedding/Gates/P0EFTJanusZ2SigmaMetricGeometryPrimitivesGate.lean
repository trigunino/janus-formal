namespace JanusFormal
namespace P0EFTJanusZ2SigmaMetricGeometryPrimitivesGate

set_option autoImplicit false

structure MetricGeometryPrimitivesGate where
  metricInverseBuilderReady : Prop
  christoffelBuilderReady : Prop
  unitNormalFromLevelSetReady : Prop
  inducedMetricPullbackReady : Prop
  requiresActiveMetric : Prop
  requiresActiveMetricDerivatives : Prop
  requiresActiveLevelSetOrEmbedding : Prop
  requiresExplicitNormalNormSign : Prop
  requiresExplicitOrientationSign : Prop
  usesPlanckLCDMInputs : Prop
  usesArchivedZ4Inputs : Prop
  metricGeometryValuesReady : Prop

def strictMetricGeometryPrimitivesReady
    (g : MetricGeometryPrimitivesGate) : Prop :=
  g.metricInverseBuilderReady /\
  g.christoffelBuilderReady /\
  g.unitNormalFromLevelSetReady /\
  g.inducedMetricPullbackReady /\
  g.requiresActiveMetric /\
  g.requiresActiveMetricDerivatives /\
  g.requiresActiveLevelSetOrEmbedding /\
  g.requiresExplicitNormalNormSign /\
  g.requiresExplicitOrientationSign /\
  ¬ g.usesPlanckLCDMInputs /\
  ¬ g.usesArchivedZ4Inputs

theorem metric_geometry_values_require_active_metric
    (g : MetricGeometryPrimitivesGate)
    (hValues : g.metricGeometryValuesReady)
    (hImplies :
      g.metricGeometryValuesReady ->
        g.requiresActiveMetric /\ g.requiresActiveMetricDerivatives) :
    g.requiresActiveMetric /\ g.requiresActiveMetricDerivatives := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaMetricGeometryPrimitivesGate
end JanusFormal

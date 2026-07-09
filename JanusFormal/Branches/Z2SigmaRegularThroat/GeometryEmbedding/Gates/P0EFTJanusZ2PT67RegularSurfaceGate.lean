namespace JanusFormal
namespace P0EFTJanusZ2PT67RegularSurfaceGate

set_option autoImplicit false

structure PT67RegularSurfaceGate where
  metricCrossTermSignFlipped : Prop
  trBlockNonDegenerateAtSigma : Prop
  inducedMetricNonDegenerate : Prop
  hAbReady : Prop
  unitNormalReady : Prop
  localKAbReady : Prop
  regularHKPipelineAllowed : Prop
  z2GluingOrientationFixed : Prop
  deltaKPlusMinusReady : Prop

def localRegularGeometryReady
    (g : PT67RegularSurfaceGate) : Prop :=
  g.metricCrossTermSignFlipped /\
  g.trBlockNonDegenerateAtSigma /\
  g.inducedMetricNonDegenerate /\
  g.hAbReady /\
  g.unitNormalReady /\
  g.localKAbReady /\
  g.regularHKPipelineAllowed

theorem deltaK_requires_gluing_orientation
    (g : PT67RegularSurfaceGate)
    (hDelta : g.deltaKPlusMinusReady)
    (hNeeds : g.deltaKPlusMinusReady -> g.z2GluingOrientationFixed) :
    g.z2GluingOrientationFixed := by
  exact hNeeds hDelta

theorem local_geometry_enables_regular_hK_pipeline
    (g : PT67RegularSurfaceGate)
    (hReady : localRegularGeometryReady g) :
    g.regularHKPipelineAllowed := by
  exact hReady.right.right.right.right.right.right

end P0EFTJanusZ2PT67RegularSurfaceGate
end JanusFormal

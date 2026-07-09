namespace JanusFormal
namespace P0EFTJanusZ2PT67GluingOrientationGate

set_option autoImplicit false

structure PT67GluingOrientationGate where
  regularSurfaceReady : Prop
  timeCovectorPTFlips : Prop
  radialCovectorPTInvariant : Prop
  normalCovectorPTInvariant : Prop
  screenMetricTransported : Prop
  extrinsicCurvaturePTInvariant : Prop
  freeOrientationSignUsed : Prop
  outwardIsraelCutPasteNormalsUsed : Prop
  deltaKPTTransportReady : Prop
  cartanGHYJumpReadyUnderPTTransport : Prop

def ptTransportRaccordReady
    (g : PT67GluingOrientationGate) : Prop :=
  g.regularSurfaceReady /\
  g.timeCovectorPTFlips /\
  g.radialCovectorPTInvariant /\
  g.normalCovectorPTInvariant /\
  g.screenMetricTransported /\
  g.extrinsicCurvaturePTInvariant /\
  Not g.freeOrientationSignUsed /\
  Not g.outwardIsraelCutPasteNormalsUsed /\
  g.deltaKPTTransportReady

theorem pt_raccord_enables_cartan_ghy_jump
    (g : PT67GluingOrientationGate)
    (_h : ptTransportRaccordReady g)
    (hNeeds : ptTransportRaccordReady g -> g.cartanGHYJumpReadyUnderPTTransport) :
    g.cartanGHYJumpReadyUnderPTTransport := by
  exact hNeeds _h

end P0EFTJanusZ2PT67GluingOrientationGate
end JanusFormal

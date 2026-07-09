namespace JanusFormal
namespace P0EFTJanusZ2SigmaPublishedBimetricActionPivotGate

set_option autoImplicit false

structure PublishedBimetricActionPivotGate where
  localSigmaCountertermFirstUnderselected : Prop
  publishedBulkBimetricActionAvailable : Prop
  determinantBridgeFactorsAvailable : Prop
  bianchiConstraintsOnSourceSlotsAvailable : Prop
  completeNonlinearInteractionTensorAvailable : Prop
  localSigmaDensityAvailable : Prop
  z2TunnelSigmaKept : Prop
  z4NotReopened : Prop
  modelChanged : Prop
  routeChanged : Prop

def pivotReady (g : PublishedBimetricActionPivotGate) : Prop :=
  g.localSigmaCountertermFirstUnderselected /\
  g.publishedBulkBimetricActionAvailable /\
  g.determinantBridgeFactorsAvailable /\
  g.bianchiConstraintsOnSourceSlotsAvailable /\
  g.z2TunnelSigmaKept /\
  g.z4NotReopened /\
  Not g.modelChanged /\
  g.routeChanged

theorem pivot_is_route_change_not_model_change
    (g : PublishedBimetricActionPivotGate)
    (h : pivotReady g) :
    Not g.modelChanged /\ g.routeChanged /\ g.z2TunnelSigmaKept := by
  exact And.intro h.right.right.right.right.right.right.left
    (And.intro h.right.right.right.right.right.right.right h.right.right.right.right.left)

theorem published_action_still_needs_nonlinear_source_or_sigma_density
    (g : PublishedBimetricActionPivotGate)
    (_h : pivotReady g)
    (hNoTensor : Not g.completeNonlinearInteractionTensorAvailable)
    (hNoSigma : Not g.localSigmaDensityAvailable) :
    Not (g.completeNonlinearInteractionTensorAvailable \/ g.localSigmaDensityAvailable) := by
  intro hEither
  rcases hEither with hTensor | hSigma
  · exact hNoTensor hTensor
  · exact hNoSigma hSigma

end P0EFTJanusZ2SigmaPublishedBimetricActionPivotGate
end JanusFormal

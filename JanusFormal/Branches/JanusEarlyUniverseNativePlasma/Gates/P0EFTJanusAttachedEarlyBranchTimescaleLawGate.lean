namespace JanusFormal
namespace P0EFTJanusAttachedEarlyBranchTimescaleLawGate

set_option autoImplicit false

structure AttachedEarlyBranchTimescaleLawGate where
  c1MatchingImported : Prop
  earlyCoshHShapeExactDeclared : Prop
  timeScaleRatioFixedByGeometry : Prop
  freeTimeScaleRatioRemoved : Prop
  aMinSelectionStillOpen : Prop
  transitionSelectionStillOpen : Prop
  physicalModelReady : Prop

def attachedTimescaleLawReady
    (g : AttachedEarlyBranchTimescaleLawGate) : Prop :=
  g.c1MatchingImported /\
  g.earlyCoshHShapeExactDeclared /\
  g.timeScaleRatioFixedByGeometry /\
  g.freeTimeScaleRatioRemoved /\
  g.aMinSelectionStillOpen /\
  g.transitionSelectionStillOpen /\
  Not g.physicalModelReady

theorem timescale_ratio_not_free_after_matching_inputs
    (g : AttachedEarlyBranchTimescaleLawGate)
    (hReady : attachedTimescaleLawReady g) :
    g.freeTimeScaleRatioRemoved /\ g.aMinSelectionStillOpen := by
  exact And.intro hReady.2.2.2.1 hReady.2.2.2.2.1

end P0EFTJanusAttachedEarlyBranchTimescaleLawGate
end JanusFormal

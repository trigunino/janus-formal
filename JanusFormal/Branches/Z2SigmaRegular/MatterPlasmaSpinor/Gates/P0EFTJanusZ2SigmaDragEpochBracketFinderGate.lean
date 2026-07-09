namespace JanusFormal
namespace P0EFTJanusZ2SigmaDragEpochBracketFinderGate

set_option autoImplicit false

structure DragEpochBracketFinderGate where
  dragEpochBracketFinderReady : Prop
  requiresActiveHZ2Sigma : Prop
  requiresActiveGammaDragZ2Sigma : Prop
  requiresActiveZGrid : Prop
  usesPlanckLCDMDragEpochFit : Prop
  usesArchivedZ4Inputs : Prop
  zDValuesReady : Prop

def strictDragEpochBracketFinderReady
    (g : DragEpochBracketFinderGate) : Prop :=
  g.dragEpochBracketFinderReady /\
  g.requiresActiveHZ2Sigma /\
  g.requiresActiveGammaDragZ2Sigma /\
  g.requiresActiveZGrid /\
  ¬ g.usesPlanckLCDMDragEpochFit /\
  ¬ g.usesArchivedZ4Inputs

theorem z_d_values_require_active_H_and_drag
    (g : DragEpochBracketFinderGate)
    (hValues : g.zDValuesReady)
    (hImplies : g.zDValuesReady -> g.requiresActiveHZ2Sigma /\ g.requiresActiveGammaDragZ2Sigma) :
    g.requiresActiveHZ2Sigma /\ g.requiresActiveGammaDragZ2Sigma := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaDragEpochBracketFinderGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2SigmaExtrinsicCurvatureJumpBuilderGate

set_option autoImplicit false

structure ExtrinsicCurvatureJumpBuilderGate where
  deltaKJumpBuilderReady : Prop
  requiresActiveKsPlusOfA : Prop
  requiresActiveKsMinusOfA : Prop
  requiresActiveKtauPlusOfA : Prop
  requiresActiveKtauMinusOfA : Prop
  requiresExplicitZ2Orientation : Prop
  usesPlanckLCDMInputs : Prop
  usesArchivedZ4Inputs : Prop
  deltaKValuesReady : Prop

def strictDeltaKJumpBuilderReady
    (g : ExtrinsicCurvatureJumpBuilderGate) : Prop :=
  g.deltaKJumpBuilderReady /\
  g.requiresActiveKsPlusOfA /\
  g.requiresActiveKsMinusOfA /\
  g.requiresActiveKtauPlusOfA /\
  g.requiresActiveKtauMinusOfA /\
  g.requiresExplicitZ2Orientation /\
  ¬ g.usesPlanckLCDMInputs /\
  ¬ g.usesArchivedZ4Inputs

theorem deltaK_values_require_active_plus_minus_curvatures
    (g : ExtrinsicCurvatureJumpBuilderGate)
    (hValues : g.deltaKValuesReady)
    (hImplies :
      g.deltaKValuesReady ->
        g.requiresActiveKsPlusOfA /\
        g.requiresActiveKsMinusOfA /\
        g.requiresActiveKtauPlusOfA /\
        g.requiresActiveKtauMinusOfA) :
    g.requiresActiveKsPlusOfA /\
    g.requiresActiveKsMinusOfA /\
    g.requiresActiveKtauPlusOfA /\
    g.requiresActiveKtauMinusOfA := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaExtrinsicCurvatureJumpBuilderGate
end JanusFormal

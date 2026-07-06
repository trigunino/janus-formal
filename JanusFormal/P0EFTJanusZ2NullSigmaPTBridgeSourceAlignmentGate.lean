namespace JanusFormal
namespace P0EFTJanusZ2NullSigmaPTBridgeSourceAlignmentGate

set_option autoImplicit false

structure NullSigmaPTBridgeSourceAlignmentGate where
  drdtCrossTermRetained : Prop
  oneWayMembraneInterpretation : Prop
  twoPTSymmetricSheets : Prop
  timeReversalAtCrossing : Prop
  orientationReversalAtCrossing : Prop
  souriauEnergyMassInversionRelevant : Prop
  projectiveP4TubularContextRelevant : Prop
  degenerateOrNullThroatAllowed : Prop
  regularHKPipelineAllowed : Prop
  standardGHYIsraelCartanPipelineAllowed : Prop
  nullBoundaryVariablesDeclared : Prop
  nullActionVariationReady : Prop
  nullJunctionBalanceReady : Prop

def sourceAlignedNullPTBranch
    (g : NullSigmaPTBridgeSourceAlignmentGate) : Prop :=
  g.drdtCrossTermRetained /\
  g.oneWayMembraneInterpretation /\
  g.twoPTSymmetricSheets /\
  g.timeReversalAtCrossing /\
  g.orientationReversalAtCrossing /\
  g.souriauEnergyMassInversionRelevant /\
  g.projectiveP4TubularContextRelevant /\
  g.degenerateOrNullThroatAllowed

theorem null_PT_branch_forbids_regular_hK_when_regular_pipeline_not_allowed
    (g : NullSigmaPTBridgeSourceAlignmentGate)
    (_h : sourceAlignedNullPTBranch g)
    (hNoHK : Not g.regularHKPipelineAllowed) :
    Not g.regularHKPipelineAllowed := by
  exact hNoHK

theorem null_junction_requires_null_variables
    (g : NullSigmaPTBridgeSourceAlignmentGate)
    (hBalance : g.nullJunctionBalanceReady)
    (hNeedsVars : g.nullJunctionBalanceReady -> g.nullBoundaryVariablesDeclared) :
    g.nullBoundaryVariablesDeclared := by
  exact hNeedsVars hBalance

end P0EFTJanusZ2NullSigmaPTBridgeSourceAlignmentGate
end JanusFormal

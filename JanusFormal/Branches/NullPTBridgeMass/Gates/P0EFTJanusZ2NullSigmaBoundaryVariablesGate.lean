namespace JanusFormal
namespace P0EFTJanusZ2NullSigmaBoundaryVariablesGate

set_option autoImplicit false

structure NullSigmaBoundaryVariablesGate where
  nullGeneratorDeclared : Prop
  auxiliaryNullDeclared : Prop
  screenMetricDeclared : Prop
  expansionDeclared : Prop
  shearDeclared : Prop
  inaffinityDeclared : Prop
  nullBoundaryVariablesDeclared : Prop
  regularHKPipelineAllowed : Prop
  nullActionVariationReady : Prop
  nullJunctionBalanceReady : Prop

def nullBoundaryVariableSetReady
    (g : NullSigmaBoundaryVariablesGate) : Prop :=
  g.nullGeneratorDeclared /\
  g.auxiliaryNullDeclared /\
  g.screenMetricDeclared /\
  g.expansionDeclared /\
  g.shearDeclared /\
  g.inaffinityDeclared /\
  g.nullBoundaryVariablesDeclared

theorem null_variables_do_not_enable_regular_hK
    (g : NullSigmaBoundaryVariablesGate)
    (_h : nullBoundaryVariableSetReady g)
    (hNoHK : Not g.regularHKPipelineAllowed) :
    Not g.regularHKPipelineAllowed := by
  exact hNoHK

theorem null_junction_requires_null_action_variation
    (g : NullSigmaBoundaryVariablesGate)
    (hBalance : g.nullJunctionBalanceReady)
    (hNeeds : g.nullJunctionBalanceReady -> g.nullActionVariationReady) :
    g.nullActionVariationReady := by
  exact hNeeds hBalance

end P0EFTJanusZ2NullSigmaBoundaryVariablesGate
end JanusFormal

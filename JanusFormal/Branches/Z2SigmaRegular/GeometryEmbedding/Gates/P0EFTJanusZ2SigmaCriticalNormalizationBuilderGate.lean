namespace JanusFormal
namespace P0EFTJanusZ2SigmaCriticalNormalizationBuilderGate

set_option autoImplicit false

structure CriticalNormalizationBuilderGate where
  criticalNormalizationBuilderReady : Prop
  requiresActiveH0Z2Sigma : Prop
  requiresExplicitGravitationalConstant : Prop
  usesPlanckLCDMH0 : Prop
  usesArchivedZ4Inputs : Prop
  criticalNormalizationValuesReady : Prop

def strictCriticalNormalizationBuilderReady
    (g : CriticalNormalizationBuilderGate) : Prop :=
  g.criticalNormalizationBuilderReady /\
  g.requiresActiveH0Z2Sigma /\
  g.requiresExplicitGravitationalConstant /\
  ¬ g.usesPlanckLCDMH0 /\
  ¬ g.usesArchivedZ4Inputs

theorem critical_values_require_active_H0
    (g : CriticalNormalizationBuilderGate)
    (hValues : g.criticalNormalizationValuesReady)
    (hImplies : g.criticalNormalizationValuesReady -> g.requiresActiveH0Z2Sigma) :
    g.requiresActiveH0Z2Sigma := by
  exact hImplies hValues

end P0EFTJanusZ2SigmaCriticalNormalizationBuilderGate
end JanusFormal

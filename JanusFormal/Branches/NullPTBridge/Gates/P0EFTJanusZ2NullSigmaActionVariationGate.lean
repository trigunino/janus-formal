namespace JanusFormal
namespace P0EFTJanusZ2NullSigmaActionVariationGate

set_option autoImplicit false

structure NullSigmaActionVariationGate where
  nullBoundaryVariablesReady : Prop
  nullDensitySqrtQKappaIdentified : Prop
  generatorParametrizationFixed : Prop
  rescalingAmbiguityRecorded : Prop
  deltaQABSlotDeclared : Prop
  deltaKappaSlotDeclared : Prop
  cornerJointVariationSlotDeclared : Prop
  regularHKPipelineAllowed : Prop
  nullActionVariationReady : Prop
  nullJunctionBalanceReady : Prop

def nullActionLedgerDeclared
    (g : NullSigmaActionVariationGate) : Prop :=
  g.nullBoundaryVariablesReady /\
  g.nullDensitySqrtQKappaIdentified /\
  g.generatorParametrizationFixed /\
  g.rescalingAmbiguityRecorded /\
  g.deltaQABSlotDeclared /\
  g.deltaKappaSlotDeclared /\
  g.cornerJointVariationSlotDeclared

theorem null_action_ledger_does_not_enable_regular_hK
    (g : NullSigmaActionVariationGate)
    (_h : nullActionLedgerDeclared g)
    (hNoHK : Not g.regularHKPipelineAllowed) :
    Not g.regularHKPipelineAllowed := by
  exact hNoHK

theorem null_junction_requires_null_action_variation
    (g : NullSigmaActionVariationGate)
    (hBalance : g.nullJunctionBalanceReady)
    (hNeeds : g.nullJunctionBalanceReady -> g.nullActionVariationReady) :
    g.nullActionVariationReady := by
  exact hNeeds hBalance

end P0EFTJanusZ2NullSigmaActionVariationGate
end JanusFormal

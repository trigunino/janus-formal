import JanusFormal.P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGate

set_option autoImplicit false

structure FixedMapPullbackVariationCommutationGate where
  connectionOnlyFixedEmbeddingVariationGateDeclared : Prop
  differentialFormPullbackLinearityChecked : Prop
  fixedSmoothMapDeclared : Prop
  connectionOneFormVariationDeclared : Prop
  pullbackActsLinearlyOnConnectionForms : Prop
  variationActsOnlyOnConnectionForm : Prop
  noMapVariationTerm : Prop
  noFittedPullbackCoefficient : Prop
  pullbackCommutesWithDeltaOmegaProved : Prop

def fixedMapPullbackVariationCommutationLedgerDeclared
    (g : FixedMapPullbackVariationCommutationGate) : Prop :=
  g.connectionOnlyFixedEmbeddingVariationGateDeclared /\
  g.differentialFormPullbackLinearityChecked /\
  g.fixedSmoothMapDeclared /\
  g.connectionOneFormVariationDeclared /\
  g.pullbackActsLinearlyOnConnectionForms /\
  g.variationActsOnlyOnConnectionForm /\
  g.noMapVariationTerm /\
  g.noFittedPullbackCoefficient

def fixedMapPullbackVariationCommutationReady
    (g : FixedMapPullbackVariationCommutationGate) : Prop :=
  fixedMapPullbackVariationCommutationLedgerDeclared g /\
  g.pullbackCommutesWithDeltaOmegaProved

theorem fixed_map_pullback_variation_commutation_ready_requires_commutation
    (g : FixedMapPullbackVariationCommutationGate)
    (hReady : fixedMapPullbackVariationCommutationReady g) :
    g.pullbackCommutesWithDeltaOmegaProved := by
  exact hReady.right

end P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGate
end JanusFormal

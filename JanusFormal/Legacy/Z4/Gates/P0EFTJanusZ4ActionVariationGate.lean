import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4TensorOperatorContract

namespace JanusFormal
namespace P0EFTJanusZ4ActionVariationGate

set_option autoImplicit false

abbrev TensorOperator :=
  P0EFTJanusZ4TensorOperatorContract.DeterminantCoupledTensorOperator

structure Z4ActionVariationGate where
  actionDensityDeclared : Prop
  measureVariationHandled : Prop
  eulerLagrangeMatchesRankOneOperator : Prop
  boundaryTermsClosed : Prop
  gaugeCompatibleVariation : Prop
  fullActionVariationClosed : Prop

def actionVariationScaffoldReady (g : Z4ActionVariationGate) : Prop :=
  g.actionDensityDeclared /\
  g.measureVariationHandled /\
  g.eulerLagrangeMatchesRankOneOperator /\
  g.boundaryTermsClosed /\
  g.gaugeCompatibleVariation

def actionVariationPromotesTensorOperator
    (g : Z4ActionVariationGate) (op : TensorOperator) : Prop :=
  actionVariationScaffoldReady g /\
  g.fullActionVariationClosed /\
  P0EFTJanusZ4TensorOperatorContract.tensorOperatorFromCoupledEquationsReady op

theorem action_scaffold_requires_el_match
    (g : Z4ActionVariationGate)
    (h : actionVariationScaffoldReady g) :
    g.eulerLagrangeMatchesRankOneOperator := by
  exact h.right.right.left

theorem action_scaffold_does_not_close_full_variation
    (g : Z4ActionVariationGate)
    (op : TensorOperator)
    (_h : actionVariationScaffoldReady g)
    (hMissing : Not g.fullActionVariationClosed) :
    Not (actionVariationPromotesTensorOperator g op) := by
  intro h
  exact hMissing h.right.left

end P0EFTJanusZ4ActionVariationGate
end JanusFormal

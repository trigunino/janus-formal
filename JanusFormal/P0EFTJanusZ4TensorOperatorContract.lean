namespace JanusFormal
namespace P0EFTJanusZ4TensorOperatorContract

set_option autoImplicit false

structure DeterminantCoupledTensorOperator where
  coupledFieldEquationsEncoded : Prop
  determinantWeightsReciprocal : Prop
  rankOneMasterSource : Prop
  plusSectorDescendsFromMaster : Prop
  minusSectorDescendsFromMaster : Prop
  independentSectorSourcesForbidden : Prop
  actionVariationDerived : Prop

def tensorOperatorFromCoupledEquationsReady
    (op : DeterminantCoupledTensorOperator) : Prop :=
  op.coupledFieldEquationsEncoded /\
  op.determinantWeightsReciprocal /\
  op.rankOneMasterSource /\
  op.plusSectorDescendsFromMaster /\
  op.minusSectorDescendsFromMaster /\
  op.independentSectorSourcesForbidden

def fullActionTensorDerivationReady
    (op : DeterminantCoupledTensorOperator) : Prop :=
  tensorOperatorFromCoupledEquationsReady op /\
  op.actionVariationDerived

theorem rank_one_operator_forbids_independent_sources
    (op : DeterminantCoupledTensorOperator)
    (h : tensorOperatorFromCoupledEquationsReady op) :
    op.rankOneMasterSource /\
    op.plusSectorDescendsFromMaster /\
    op.minusSectorDescendsFromMaster /\
    op.independentSectorSourcesForbidden := by
  exact ⟨h.right.right.left,
    h.right.right.right.left,
    h.right.right.right.right.left,
    h.right.right.right.right.right⟩

theorem coupled_equations_do_not_imply_action_variation
    (op : DeterminantCoupledTensorOperator)
    (_h : tensorOperatorFromCoupledEquationsReady op)
    (hMissing : Not op.actionVariationDerived) :
    Not (fullActionTensorDerivationReady op) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4TensorOperatorContract
end JanusFormal

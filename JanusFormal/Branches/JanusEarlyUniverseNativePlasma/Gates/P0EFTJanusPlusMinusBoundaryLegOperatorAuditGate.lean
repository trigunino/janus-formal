import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusBoundaryHamiltonianScalarVsOperatorAuditGate

namespace JanusFormal
namespace P0EFTJanusPlusMinusBoundaryLegOperatorAuditGate

set_option autoImplicit false

structure PlusMinusBoundaryLegOperatorAuditGate where
  plusMinusLegOperatorAvailable : Prop
  legOperatorHasAtMostTwoLevels : Prop
  legOperatorAloneOrders1001States : Prop
  legOperatorCanBePTDoubletFactor : Prop
  sym4InternalTransferDerived : Prop
  full1001OrderingClosed : Prop

def plusMinusLegRouteClosed
    (g : PlusMinusBoundaryLegOperatorAuditGate) : Prop :=
  g.plusMinusLegOperatorAvailable /\
  g.legOperatorAloneOrders1001States /\
  g.full1001OrderingClosed

def plusMinusLegRouteFrontier
    (g : PlusMinusBoundaryLegOperatorAuditGate) : Prop :=
  g.plusMinusLegOperatorAvailable /\
  g.legOperatorHasAtMostTwoLevels /\
  Not g.legOperatorAloneOrders1001States /\
  g.legOperatorCanBePTDoubletFactor /\
  Not g.sym4InternalTransferDerived /\
  Not g.full1001OrderingClosed

theorem two_leg_operator_alone_cannot_close_1001_ordering
    (g : PlusMinusBoundaryLegOperatorAuditGate)
    (hFrontier : plusMinusLegRouteFrontier g) :
    Not (plusMinusLegRouteClosed g) := by
  intro h
  exact hFrontier.2.2.1 h.2.1

end P0EFTJanusPlusMinusBoundaryLegOperatorAuditGate
end JanusFormal

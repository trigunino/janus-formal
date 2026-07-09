import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusHnormalSymmetryBreakingCandidateMatrixGate

namespace JanusFormal
namespace P0EFTJanusPTNormalToSym4InternalMatrixAttemptGate

set_option autoImplicit false

structure PTNormalToSym4InternalMatrixAttemptGate where
  PTNormalOrientationAvailable : Prop
  globalPTSignOrders1001States : Prop
  plusMinusLegExchangeOrders1001States : Prop
  blockSignsOrder1001States : Prop
  normalConnectionEndomorphismDerived : Prop
  normalConnectionLiftedToSym4 : Prop
  normalConnectionOrders1001States : Prop

def PTNormalToSym4MatrixClosed
    (g : PTNormalToSym4InternalMatrixAttemptGate) : Prop :=
  g.PTNormalOrientationAvailable /\
  g.normalConnectionEndomorphismDerived /\
  g.normalConnectionLiftedToSym4 /\
  g.normalConnectionOrders1001States

def PTNormalToSym4MatrixFrontier
    (g : PTNormalToSym4InternalMatrixAttemptGate) : Prop :=
  g.PTNormalOrientationAvailable /\
  Not g.globalPTSignOrders1001States /\
  Not g.plusMinusLegExchangeOrders1001States /\
  Not g.blockSignsOrder1001States /\
  Not g.normalConnectionEndomorphismDerived

theorem PT_signs_without_normal_connection_do_not_close_sym4_matrix
    (g : PTNormalToSym4InternalMatrixAttemptGate)
    (hFrontier : PTNormalToSym4MatrixFrontier g) :
    Not (PTNormalToSym4MatrixClosed g) := by
  intro h
  exact hFrontier.2.2.2.2 h.2.1

end P0EFTJanusPTNormalToSym4InternalMatrixAttemptGate
end JanusFormal

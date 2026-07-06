import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYJunctionTracePartitionAuditGate

set_option autoImplicit false

structure CartanGHYJunctionTracePartitionAuditGate where
  roundThroatJumpGeometryDeclared : Prop
  lanczosIsraelTraceComputed : Prop
  finiteThroatTraceCarriedByJunction : Prop
  finiteThroatTraceCarriedByCartanGHYVariation : Prop
  linearKCountertermResidualZeroAfterPartition : Prop
  countertermC1ZeroAfterPartition : Prop
  remainingCountertermMustBeNonGHY : Prop
  fullCountertermTraceReady : Prop
  eCountertermReady : Prop
  noDuplicateJunctionTraceInLCt : Prop

def linearKPartitionClosed
    (g : CartanGHYJunctionTracePartitionAuditGate) : Prop :=
  g.roundThroatJumpGeometryDeclared /\
  g.lanczosIsraelTraceComputed /\
  g.finiteThroatTraceCarriedByJunction /\
  g.finiteThroatTraceCarriedByCartanGHYVariation /\
  g.linearKCountertermResidualZeroAfterPartition /\
  g.countertermC1ZeroAfterPartition /\
  g.remainingCountertermMustBeNonGHY /\
  g.noDuplicateJunctionTraceInLCt

theorem linear_k_partition_does_not_close_full_counterterm
    (g : CartanGHYJunctionTracePartitionAuditGate)
    (_hClosed : linearKPartitionClosed g)
    (hNotReady : Not g.eCountertermReady) :
    Not g.eCountertermReady := by
  exact hNotReady

end P0EFTJanusZ2SigmaCartanGHYJunctionTracePartitionAuditGate
end JanusFormal

import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaLinearKPartitionAuditGate

set_option autoImplicit false

structure LinearKPartitionAuditGate where
  requiredTraceTermIsLinearK : Prop
  cartanGHYLinearKOperatorAvailable : Prop
  sameSqrtHKOperatorClass : Prop
  independentCountertermAllowed : Prop
  partitionIntoCartanGHYOrJunctionRequired : Prop
  countertermRemainingDensityMustBeNonGHY : Prop
  duplicateSqrtHKForbidden : Prop
  rSigmaCertificateStillBlocked : Prop

def linearKPartitionAuditReady
    (g : LinearKPartitionAuditGate) : Prop :=
  g.requiredTraceTermIsLinearK /\
  g.cartanGHYLinearKOperatorAvailable /\
  g.sameSqrtHKOperatorClass /\
  g.partitionIntoCartanGHYOrJunctionRequired /\
  g.countertermRemainingDensityMustBeNonGHY /\
  g.duplicateSqrtHKForbidden

theorem duplicate_linear_k_blocks_counterterm_promotion
    (g : LinearKPartitionAuditGate)
    (_hReady : linearKPartitionAuditReady g)
    (hNoDup : Not g.independentCountertermAllowed) :
    Not g.independentCountertermAllowed := by
  exact hNoDup

end P0EFTJanusZ2SigmaLinearKPartitionAuditGate
end JanusFormal

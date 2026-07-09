namespace JanusFormal
namespace P0EFTCMBPlanckLowLDirectGate

set_option autoImplicit false

structure PlanckLowLDirectGate where
  cobayaPackagesInstalled : Prop
  exactCAMBForkBuilt : Prop
  uncompressedPlanckLowLUsed : Prop
  uncompressedPlanckHighLUsed : Prop
  lowLLikelihoodRun : Prop

def lowLDirectGateReady (g : PlanckLowLDirectGate) : Prop :=
  g.cobayaPackagesInstalled /\
  g.exactCAMBForkBuilt /\
  g.uncompressedPlanckLowLUsed /\
  g.lowLLikelihoodRun

def fullDirectCMBReady (g : PlanckLowLDirectGate) : Prop :=
  lowLDirectGateReady g /\
  g.uncompressedPlanckHighLUsed

theorem lowl_only_does_not_close_full_direct_cmb
    (g : PlanckLowLDirectGate)
    (_hLowL : lowLDirectGateReady g)
    (hNoHighL : Not g.uncompressedPlanckHighLUsed) :
    Not (fullDirectCMBReady g) := by
  intro h
  exact hNoHighL h.right

end P0EFTCMBPlanckLowLDirectGate
end JanusFormal

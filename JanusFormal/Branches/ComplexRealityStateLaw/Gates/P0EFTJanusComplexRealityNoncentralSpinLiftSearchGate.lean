import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityAroundSigmaCP1HolonomyActionGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityNoncentralSpinLiftSearchGate

set_option autoImplicit false

structure NoncentralSpinLiftSearchGate where
  aroundSigmaZ2CycleClosed : Prop
  spinorProjectionReadinessDeclared : Prop
  resolvedTunnelPinLiftReady : Prop
  globalSpinorProjectionReady : Prop
  noncentralLiftForcedByGeometry : Prop
  noncentralLiftAxisDerived : Prop

def searchComplete (g : NoncentralSpinLiftSearchGate) : Prop :=
  g.aroundSigmaZ2CycleClosed /\ g.spinorProjectionReadinessDeclared

def noncentralSpinLiftDerived (g : NoncentralSpinLiftSearchGate) : Prop :=
  searchComplete g /\
  g.resolvedTunnelPinLiftReady /\
  g.globalSpinorProjectionReady /\
  g.noncentralLiftForcedByGeometry /\
  g.noncentralLiftAxisDerived

theorem no_forced_noncentral_lift_blocks_derivation
    (g : NoncentralSpinLiftSearchGate)
    (hMissing : Not g.noncentralLiftForcedByGeometry) :
    Not (noncentralSpinLiftDerived g) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTJanusComplexRealityNoncentralSpinLiftSearchGate
end JanusFormal

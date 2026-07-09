import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityBoundaryVariationBasisGate
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusAroundSigmaZ2CycleTransportGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityClosedBoundaryTwoCycleGate

set_option autoImplicit false

structure ClosedBoundaryTwoCycleGate where
  aroundSigmaZ2CycleClosed : Prop
  topologicalThroatS2Closed : Prop
  finiteCoadjointOrbitTwoCycleClosed : Prop
  symbolicBoundaryVariationBasisReady : Prop
  activeBoundaryVariationBasisReady : Prop
  closedKKSPhaseSpaceTwoCycleDeclared : Prop
  nonzeroKKSPullbackPeriodComputed : Prop
  alphaGenerated : Prop

def topologicalCycleAuditReady (g : ClosedBoundaryTwoCycleGate) : Prop :=
  g.aroundSigmaZ2CycleClosed /\
  g.topologicalThroatS2Closed /\
  g.finiteCoadjointOrbitTwoCycleClosed /\
  g.symbolicBoundaryVariationBasisReady

def kksBoundaryTwoCycleReady (g : ClosedBoundaryTwoCycleGate) : Prop :=
  topologicalCycleAuditReady g /\
  g.activeBoundaryVariationBasisReady /\
  g.closedKKSPhaseSpaceTwoCycleDeclared /\
  g.nonzeroKKSPullbackPeriodComputed

def alphaGeneratedFromKKSPeriod (g : ClosedBoundaryTwoCycleGate) : Prop :=
  kksBoundaryTwoCycleReady g /\ g.alphaGenerated

theorem z2_one_cycle_and_throat_s2_do_not_imply_kks_period
    (g : ClosedBoundaryTwoCycleGate)
    (hMissing : Not g.closedKKSPhaseSpaceTwoCycleDeclared) :
    Not (kksBoundaryTwoCycleReady g) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_nonzero_period_blocks_alpha
    (g : ClosedBoundaryTwoCycleGate)
    (hMissing : Not g.nonzeroKKSPullbackPeriodComputed) :
    Not (alphaGeneratedFromKKSPeriod g) := by
  intro h
  exact hMissing h.left.right.right.right

end P0EFTJanusComplexRealityClosedBoundaryTwoCycleGate
end JanusFormal

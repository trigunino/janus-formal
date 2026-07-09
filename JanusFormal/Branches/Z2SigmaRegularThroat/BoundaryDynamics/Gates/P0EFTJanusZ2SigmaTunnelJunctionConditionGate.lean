import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelCoverSurvivalGate
import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaProjectedStressTensorGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTunnelJunctionConditionGate

set_option autoImplicit false

structure Z2SigmaTunnelJunctionConditionGate where
  projectedSigmaStressTensorDerived : Prop
  twoFoldCoverSurvivesTunnelSurgery : Prop
  sigmaNormalOrientationDeclared : Prop
  extrinsicCurvatureJumpDeclared : Prop
  lanczosIsraelLikeJumpEquationDeclared : Prop
  z2OrientationReversalIncluded : Prop
  noAntipodalFixedPointShell : Prop
  z2TunnelJunctionConditionDerived : Prop

def tunnelJunctionLockClosed
    (g : Z2SigmaTunnelJunctionConditionGate) : Prop :=
  g.projectedSigmaStressTensorDerived /\
  g.twoFoldCoverSurvivesTunnelSurgery /\
  g.sigmaNormalOrientationDeclared /\
  g.extrinsicCurvatureJumpDeclared /\
  g.lanczosIsraelLikeJumpEquationDeclared /\
  g.z2OrientationReversalIncluded /\
  g.noAntipodalFixedPointShell

theorem tunnel_junction_lock_derives_condition
    (g : Z2SigmaTunnelJunctionConditionGate)
    (hLock : tunnelJunctionLockClosed g)
    (hImplies : tunnelJunctionLockClosed g -> g.z2TunnelJunctionConditionDerived) :
    g.z2TunnelJunctionConditionDerived := by
  exact hImplies hLock

end P0EFTJanusZ2SigmaTunnelJunctionConditionGate
end JanusFormal

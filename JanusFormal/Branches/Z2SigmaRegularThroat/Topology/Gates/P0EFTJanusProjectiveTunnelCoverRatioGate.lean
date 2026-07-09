import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelCoverSurvivalGate
import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelVolumeRatioGate

namespace JanusFormal
namespace P0EFTJanusProjectiveTunnelCoverRatioGate

set_option autoImplicit false

structure ProjectiveTunnelCoverRatioGate where
  projectiveTunnelClosed : Prop
  z2CoverInterfaceDefined : Prop
  throatSigmaDefined : Prop
  aroundSigmaCycleDefined : Prop
  localTwoToOneMultiplicityAvailable : Prop
  twoFoldCoverSurvivesTunnelSurgery : Prop
  globalCoverRatioTwoToOneComputed : Prop
  globalCoverRatioUnique : Prop
  coverRatioDerived : Prop

def localProjectiveTunnelRatioReady
    (g : ProjectiveTunnelCoverRatioGate) : Prop :=
  g.projectiveTunnelClosed /\
  g.z2CoverInterfaceDefined /\
  g.throatSigmaDefined /\
  g.aroundSigmaCycleDefined /\
  g.localTwoToOneMultiplicityAvailable /\
  g.twoFoldCoverSurvivesTunnelSurgery

def globalProjectiveTunnelRatioClosed
    (g : ProjectiveTunnelCoverRatioGate) : Prop :=
  localProjectiveTunnelRatioReady g /\
  g.globalCoverRatioTwoToOneComputed /\
  g.globalCoverRatioUnique

theorem missing_global_ratio_blocks_projective_tunnel_ratio
    (g : ProjectiveTunnelCoverRatioGate)
    (hMissing : Not g.globalCoverRatioTwoToOneComputed) :
    Not (globalProjectiveTunnelRatioClosed g) := by
  intro h
  exact hMissing h.2.1

theorem projective_tunnel_ratio_transports_to_cover_ratio
    (g : ProjectiveTunnelCoverRatioGate)
    (h : globalProjectiveTunnelRatioClosed g)
    (hTransport : globalProjectiveTunnelRatioClosed g -> g.coverRatioDerived) :
    g.coverRatioDerived := by
  exact hTransport h

end P0EFTJanusProjectiveTunnelCoverRatioGate
end JanusFormal

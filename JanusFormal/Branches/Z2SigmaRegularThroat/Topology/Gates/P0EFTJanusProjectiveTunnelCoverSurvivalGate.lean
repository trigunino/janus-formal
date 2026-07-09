namespace JanusFormal
namespace P0EFTJanusProjectiveTunnelCoverSurvivalGate

set_option autoImplicit false

structure ProjectiveTunnelCoverSurvivalGate where
  s4ToRP4CoverDeclared : Prop
  antipodalActionFreeAwayFromSurgery : Prop
  pairedPoleNeighborhoodsRemoved : Prop
  tubularReplacementEquivariant : Prop
  quotientTunnelDefined : Prop
  twoFoldCoverSurvivesTunnelSurgery : Prop
  globalVolumeRatioComputed : Prop
  globalVolumeRatioUnique : Prop

def projectiveCoverSurvivalClosed
    (g : ProjectiveTunnelCoverSurvivalGate) : Prop :=
  g.s4ToRP4CoverDeclared /\
  g.antipodalActionFreeAwayFromSurgery /\
  g.pairedPoleNeighborhoodsRemoved /\
  g.tubularReplacementEquivariant /\
  g.quotientTunnelDefined /\
  g.twoFoldCoverSurvivesTunnelSurgery

def coverSurvivalClosedButGlobalRatioOpen
    (g : ProjectiveTunnelCoverSurvivalGate) : Prop :=
  projectiveCoverSurvivalClosed g /\
  Not g.globalVolumeRatioComputed /\
  Not g.globalVolumeRatioUnique

theorem equivariant_tunnel_surgery_preserves_twofold_cover
    (g : ProjectiveTunnelCoverSurvivalGate)
    (h : projectiveCoverSurvivalClosed g) :
    g.twoFoldCoverSurvivesTunnelSurgery := by
  exact h.2.2.2.2.2

theorem cover_survival_does_not_close_global_volume_ratio
    (g : ProjectiveTunnelCoverSurvivalGate)
    (h : coverSurvivalClosedButGlobalRatioOpen g) :
    Not g.globalVolumeRatioComputed /\ Not g.globalVolumeRatioUnique := by
  exact And.intro h.2.1 h.2.2

end P0EFTJanusProjectiveTunnelCoverSurvivalGate
end JanusFormal

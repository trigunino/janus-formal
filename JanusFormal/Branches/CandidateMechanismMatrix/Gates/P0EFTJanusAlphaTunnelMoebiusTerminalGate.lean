namespace JanusFormal
namespace P0EFTJanusAlphaTunnelMoebiusTerminalGate

set_option autoImplicit false

structure AlphaTunnelMoebiusTerminalGate where
  alternativeTunnelGeometryAudited : Prop
  moebiusTwistedThroatAudited : Prop
  topologyCycleCandidatesAvailable : Prop
  activeJanusActionDerived : Prop
  nonzeroBoundaryPeriodDerived : Prop
  dimensionfulScaleDerived : Prop
  alphaSelectorDerived : Prop

def tunnelMoebiusTerminalButBlocked (g : AlphaTunnelMoebiusTerminalGate) : Prop :=
  g.alternativeTunnelGeometryAudited /\
  g.moebiusTwistedThroatAudited /\
  g.topologyCycleCandidatesAvailable /\
  Not g.activeJanusActionDerived /\
  Not g.nonzeroBoundaryPeriodDerived /\
  Not g.dimensionfulScaleDerived /\
  Not g.alphaSelectorDerived

theorem topology_cycles_alone_do_not_select_alpha
    (g : AlphaTunnelMoebiusTerminalGate)
    (h : tunnelMoebiusTerminalButBlocked g) :
    Not g.alphaSelectorDerived := by
  exact h.right.right.right.right.right.right

end P0EFTJanusAlphaTunnelMoebiusTerminalGate
end JanusFormal

namespace JanusFormal
namespace P0EFTCoherentImmirziPlanckChannelDelta

set_option autoImplicit false

structure CoherentImmirziPlanckChannelDelta where
  rawPlanckChannelsRun : Prop
  worstChannelIsHighL : Prop
  highLResidualPositive : Prop
  planckAccepted : Prop

def highLDiagnosticBlocksNoFit (d : CoherentImmirziPlanckChannelDelta) : Prop :=
  d.rawPlanckChannelsRun /\ d.worstChannelIsHighL /\ d.highLResidualPositive

def noFitReady (d : CoherentImmirziPlanckChannelDelta) : Prop :=
  d.rawPlanckChannelsRun /\ d.planckAccepted

theorem high_l_residual_blocks_acceptance
    (d : CoherentImmirziPlanckChannelDelta)
    (_hDiag : highLDiagnosticBlocksNoFit d)
    (hReject : Not d.planckAccepted) :
    Not (noFitReady d) := by
  intro h
  exact hReject h.right

end P0EFTCoherentImmirziPlanckChannelDelta
end JanusFormal

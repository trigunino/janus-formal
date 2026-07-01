import JanusFormal.P0EFTJanusZ4NativeTransferSolver

namespace JanusFormal
namespace P0EFTJanusZ4CobayaPlanckChannelGate

set_option autoImplicit false

structure CobayaPlanckChannelGate where
  highlTTChannelDeclared : Prop
  highlTEChannelDeclared : Prop
  highlEEChannelDeclared : Prop
  lowEChannelDeclared : Prop
  lensingChannelDeclared : Prop
  nativeZ4ProviderUsed : Prop
  officialPlanckLikelihoodNotClaimed : Prop

def cobayaPlanckChannelGateReady (g : CobayaPlanckChannelGate) : Prop :=
  g.highlTTChannelDeclared /\
  g.highlTEChannelDeclared /\
  g.highlEEChannelDeclared /\
  g.lowEChannelDeclared /\
  g.lensingChannelDeclared /\
  g.nativeZ4ProviderUsed /\
  g.officialPlanckLikelihoodNotClaimed

theorem channel_gate_uses_native_provider
    (g : CobayaPlanckChannelGate)
    (h : cobayaPlanckChannelGateReady g) :
    g.nativeZ4ProviderUsed := by
  exact h.right.right.right.right.right.left

end P0EFTJanusZ4CobayaPlanckChannelGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermAlphaResZ2AntiInvarianceObligationGate

set_option autoImplicit false

structure AlphaResZ2AntiInvarianceObligationGate where
  z2OrientationReversalAvailable : Prop
  alphaResComponentDecompositionAvailable : Prop
  alphaResComponentsAvailable : Prop
  alphaResComponentValuesAvailable : Prop
  componentwiseChannelClosureReady : Prop
  allEmittedComponentsOdd : Prop
  alphaResZ2AntiInvarianceProved : Prop
  pairedSheetResidualSupportProved : Prop
  quotientProjectionCancelsAlphaRes : Prop
  eCountertermZeroWithoutDensity : Prop

def antiInvarianceReady
    (g : AlphaResZ2AntiInvarianceObligationGate) : Prop :=
  g.z2OrientationReversalAvailable /\
  g.alphaResComponentDecompositionAvailable /\
  g.alphaResComponentsAvailable /\
  g.componentwiseChannelClosureReady /\
  g.allEmittedComponentsOdd /\
  g.alphaResZ2AntiInvarianceProved

def quotientCancellationReady
    (g : AlphaResZ2AntiInvarianceObligationGate) : Prop :=
  antiInvarianceReady g /\
  g.pairedSheetResidualSupportProved /\
  g.quotientProjectionCancelsAlphaRes

theorem missing_alpha_components_blocks_anti_invariance
    (g : AlphaResZ2AntiInvarianceObligationGate)
    (hMissing : Not g.alphaResComponentsAvailable) :
    Not (antiInvarianceReady g) := by
  intro hReady
  exact hMissing hReady.2.2.1

theorem missing_component_parity_blocks_anti_invariance
    (g : AlphaResZ2AntiInvarianceObligationGate)
    (hMissing : Not g.allEmittedComponentsOdd) :
    Not (antiInvarianceReady g) := by
  intro hReady
  exact hMissing hReady.2.2.2.2.1

theorem componentwise_odd_components_give_alpha_res_anti_invariance
    (g : AlphaResZ2AntiInvarianceObligationGate)
    (hReady :
      g.z2OrientationReversalAvailable /\
      g.alphaResComponentDecompositionAvailable /\
      g.alphaResComponentsAvailable /\
      g.componentwiseChannelClosureReady /\
      g.allEmittedComponentsOdd)
    (hTransport :
      g.z2OrientationReversalAvailable /\
      g.alphaResComponentDecompositionAvailable /\
      g.alphaResComponentsAvailable /\
      g.componentwiseChannelClosureReady /\
      g.allEmittedComponentsOdd -> g.alphaResZ2AntiInvarianceProved) :
    g.alphaResZ2AntiInvarianceProved := by
  exact hTransport hReady

theorem quotient_cancellation_requires_anti_invariance
    (g : AlphaResZ2AntiInvarianceObligationGate)
    (hReady : quotientCancellationReady g) :
    antiInvarianceReady g := by
  exact hReady.1

theorem counterterm_zero_requires_quotient_cancellation
    (g : AlphaResZ2AntiInvarianceObligationGate)
    (hZero : g.eCountertermZeroWithoutDensity)
    (hNeedsCancellation :
      g.eCountertermZeroWithoutDensity -> quotientCancellationReady g) :
    quotientCancellationReady g := by
  exact hNeedsCancellation hZero

end P0EFTJanusZ2SigmaCountertermAlphaResZ2AntiInvarianceObligationGate
end JanusFormal

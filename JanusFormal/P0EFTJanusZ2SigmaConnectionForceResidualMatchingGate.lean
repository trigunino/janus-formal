import JanusFormal.P0EFTJanusZ2SigmaDeterminantGradientDivergenceGate
import JanusFormal.P0EFTJanusZ2SigmaTransportCompatibilityConditionalClosureGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaConnectionForceResidualMatchingGate

set_option autoImplicit false

structure ConnectionForceResidualMatchingGate where
  determinantGradientDivergenceGateImported : Prop
  transportCompatibilityConditionalClosureGateImported : Prop
  connectionDifferenceTensorDeclared : Prop
  plusReceiverConnectionForceDeclared : Prop
  minusReceiverConnectionForceDeclared : Prop
  plusDeterminantGradientTermDeclared : Prop
  minusDeterminantGradientTermDeclared : Prop
  sameBridgeForConnectionAndStress : Prop
  noConnectionForceDrop : Prop
  noQcrossAbsorption : Prop
  determinantGradientSplitReady : Prop
  plusResidualMatchingEquationWritten : Prop
  minusResidualMatchingEquationWritten : Prop
  sourceForceEquationsDerived : Prop
  plusConnectionForceMatched : Prop
  minusConnectionForceMatched : Prop
  feedsPlusTransportCompatibility : Prop
  feedsMinusTransportCompatibility : Prop

def connectionForceMatchingTargetReady
    (g : ConnectionForceResidualMatchingGate) : Prop :=
  g.determinantGradientDivergenceGateImported /\
  g.transportCompatibilityConditionalClosureGateImported /\
  g.connectionDifferenceTensorDeclared /\
  g.plusReceiverConnectionForceDeclared /\
  g.minusReceiverConnectionForceDeclared /\
  g.plusDeterminantGradientTermDeclared /\
  g.minusDeterminantGradientTermDeclared /\
  g.sameBridgeForConnectionAndStress /\
  g.noConnectionForceDrop /\
  g.noQcrossAbsorption /\
  g.plusResidualMatchingEquationWritten /\
  g.minusResidualMatchingEquationWritten

def connectionForceResidualMatchingReady
    (g : ConnectionForceResidualMatchingGate) : Prop :=
  connectionForceMatchingTargetReady g /\
  g.determinantGradientSplitReady /\
  g.sourceForceEquationsDerived /\
  g.plusConnectionForceMatched /\
  g.minusConnectionForceMatched /\
  g.feedsPlusTransportCompatibility /\
  g.feedsMinusTransportCompatibility

theorem connection_force_matching_feeds_transport_compatibility
    (g : ConnectionForceResidualMatchingGate)
    (hReady : connectionForceResidualMatchingReady g) :
    g.feedsPlusTransportCompatibility /\ g.feedsMinusTransportCompatibility := by
  exact And.intro hReady.right.right.right.right.right.left
    hReady.right.right.right.right.right.right

theorem missing_source_force_equations_block_matching
    (g : ConnectionForceResidualMatchingGate)
    (hMissing : Not g.sourceForceEquationsDerived) :
    Not (connectionForceResidualMatchingReady g) := by
  intro hReady
  exact hMissing hReady.right.right.left

theorem connection_force_target_keeps_forces_explicit
    (g : ConnectionForceResidualMatchingGate)
    (hTarget : connectionForceMatchingTargetReady g) :
    g.noConnectionForceDrop /\ g.noQcrossAbsorption /\
      g.sameBridgeForConnectionAndStress := by
  exact And.intro hTarget.right.right.right.right.right.right.right.right.left
    (And.intro hTarget.right.right.right.right.right.right.right.right.right.left
      hTarget.right.right.right.right.right.right.right.left)

end P0EFTJanusZ2SigmaConnectionForceResidualMatchingGate
end JanusFormal

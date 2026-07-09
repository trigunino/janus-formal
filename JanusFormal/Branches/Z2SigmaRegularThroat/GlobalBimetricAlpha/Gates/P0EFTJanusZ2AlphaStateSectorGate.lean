namespace JanusFormal
namespace P0EFTJanusZ2AlphaStateSectorGate

set_option autoImplicit false

structure AlphaStateSectorGate where
  exactSolutionAlphaExists : Prop
  alphaStateSectorProvided : Prop
  alphaDeclaredIntegrationConstant : Prop
  alphaClaimedTopologyPrediction : Prop
  usesObservationFit : Prop
  usesLegacyZ4 : Prop

def stateConditionalReady (g : AlphaStateSectorGate) : Prop :=
  g.exactSolutionAlphaExists /\
  g.alphaStateSectorProvided /\
  g.alphaDeclaredIntegrationConstant /\
  Not g.alphaClaimedTopologyPrediction /\
  Not g.usesObservationFit /\
  Not g.usesLegacyZ4

theorem missing_state_blocks_ready
    (g : AlphaStateSectorGate)
    (hMissing : Not g.alphaStateSectorProvided) :
    Not (stateConditionalReady g) := by
  intro h
  exact hMissing h.right.left

theorem topology_claim_blocks_ready
    (g : AlphaStateSectorGate)
    (hClaim : g.alphaClaimedTopologyPrediction) :
    Not (stateConditionalReady g) := by
  intro h
  exact h.right.right.right.left hClaim

end P0EFTJanusZ2AlphaStateSectorGate
end JanusFormal

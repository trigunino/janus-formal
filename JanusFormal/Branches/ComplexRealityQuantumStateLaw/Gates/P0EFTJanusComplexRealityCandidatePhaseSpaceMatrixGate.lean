namespace JanusFormal
namespace P0EFTJanusComplexRealityCandidatePhaseSpaceMatrixGate

set_option autoImplicit false

structure CandidatePhaseSpaceMatrixGate where
  activeThroatS2CandidateListed : Prop
  cp1SpinorFrameCandidateListed : Prop
  aroundSigmaCompactPhaseCandidateListed : Prop
  extensionPolicyDeclared : Prop
  extensionMustProduceKKSPeriod : Prop
  alphaGenerated : Prop

def matrixReady (g : CandidatePhaseSpaceMatrixGate) : Prop :=
  g.activeThroatS2CandidateListed /\
  g.cp1SpinorFrameCandidateListed /\
  g.aroundSigmaCompactPhaseCandidateListed /\
  g.extensionPolicyDeclared /\
  g.extensionMustProduceKKSPeriod /\
  Not g.alphaGenerated

theorem matrix_listing_does_not_generate_alpha
    (g : CandidatePhaseSpaceMatrixGate)
    (h : matrixReady g) :
    Not g.alphaGenerated := by
  exact h.right.right.right.right.right

end P0EFTJanusComplexRealityCandidatePhaseSpaceMatrixGate
end JanusFormal

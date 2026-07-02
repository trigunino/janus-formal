import JanusFormal.P0EFTJanusZ4HighLDecomposedCandidatePromotionGate

namespace JanusFormal
namespace P0EFTJanusZ4CandidateNuisanceForegroundPolicyGate

set_option autoImplicit false

structure NuisanceForegroundPolicyGate where
  sameNuisanceVectorForGRAndCandidate : Prop
  foregroundParametersDeclaredByClikWrappers : Prop
  calibrationParametersDeclaredByClikWrappers : Prop
  globalNuisanceProfilingPerformed : Prop
  candidateConditionalOnComponentReferenceNuisance : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  policyGatePassed : Prop

def fixedNuisancePolicyReady (g : NuisanceForegroundPolicyGate) : Prop :=
  g.sameNuisanceVectorForGRAndCandidate /\
  g.foregroundParametersDeclaredByClikWrappers /\
  g.calibrationParametersDeclaredByClikWrappers /\
  Not g.globalNuisanceProfilingPerformed /\
  g.candidateConditionalOnComponentReferenceNuisance /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem fixed_nuisance_policy_passes_gate
    (g : NuisanceForegroundPolicyGate)
    (hPolicy : fixedNuisancePolicyReady g -> g.policyGatePassed)
    (h : fixedNuisancePolicyReady g) :
    g.policyGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4CandidateNuisanceForegroundPolicyGate
end JanusFormal

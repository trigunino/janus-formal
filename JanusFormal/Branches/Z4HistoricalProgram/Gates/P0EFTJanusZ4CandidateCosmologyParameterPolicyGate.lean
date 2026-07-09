import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4BoundarySafeNuisanceProfilingGate

namespace JanusFormal
namespace P0EFTJanusZ4CandidateCosmologyParameterPolicyGate

set_option autoImplicit false

structure CosmologyParameterPolicyGate where
  boundarySafeLocalProfiledCandidate : Prop
  backendUsesStaticSpectraTables : Prop
  cosmologicalTransferRegenerationAvailable : Prop
  standardCosmologyProfiled : Prop
  lambdaFrozen : Prop
  noNewPhysics : Prop
  noLambdaRetuning : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  policyGatePassed : Prop

def cosmologyPolicyReady (g : CosmologyParameterPolicyGate) : Prop :=
  g.boundarySafeLocalProfiledCandidate /\
  g.backendUsesStaticSpectraTables /\
  Not g.cosmologicalTransferRegenerationAvailable /\
  Not g.standardCosmologyProfiled /\
  g.lambdaFrozen /\
  g.noNewPhysics /\
  g.noLambdaRetuning /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem cosmology_policy_passes_gate
    (g : CosmologyParameterPolicyGate)
    (hPolicy : cosmologyPolicyReady g -> g.policyGatePassed)
    (h : cosmologyPolicyReady g) :
    g.policyGatePassed := by
  exact hPolicy h

end P0EFTJanusZ4CandidateCosmologyParameterPolicyGate
end JanusFormal

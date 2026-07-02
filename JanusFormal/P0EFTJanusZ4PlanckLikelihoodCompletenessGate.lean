import JanusFormal.P0EFTJanusZ4OfficialPlanckClosedBoltzmannAcousticPolarizationTrial

namespace JanusFormal
namespace P0EFTJanusZ4PlanckLikelihoodCompletenessGate

set_option autoImplicit false

structure PlanckLikelihoodCompletenessGate where
  highlTTAvailable : Prop
  highlTTTEEEAvailable : Prop
  highlTEStandaloneAvailable : Prop
  highlEEStandaloneAvailable : Prop
  lowlTTAvailable : Prop
  lowlEEAvailable : Prop
  lensingAvailable : Prop
  nuisanceParametersHandledConsistently : Prop
  foregroundModelFixedOrDeclared : Prop
  candidateTrialAllowed : Prop
  fullPlanckValidationAllowed : Prop
  generatedOutputsNotImportedAsSources : Prop
  gatePassed : Prop

def candidateLikelihoodReady (g : PlanckLikelihoodCompletenessGate) : Prop :=
  g.highlTTAvailable /\
  g.highlTTTEEEAvailable /\
  Not g.highlTEStandaloneAvailable /\
  Not g.highlEEStandaloneAvailable /\
  g.lowlTTAvailable /\
  g.lowlEEAvailable /\
  g.lensingAvailable /\
  g.nuisanceParametersHandledConsistently /\
  g.foregroundModelFixedOrDeclared /\
  g.candidateTrialAllowed /\
  Not g.fullPlanckValidationAllowed /\
  g.generatedOutputsNotImportedAsSources

theorem candidate_ready_implies_completeness_gate
    (g : PlanckLikelihoodCompletenessGate)
    (hPolicy : candidateLikelihoodReady g -> g.gatePassed)
    (h : candidateLikelihoodReady g) :
    g.gatePassed := by
  exact hPolicy h

theorem missing_standalone_teee_blocks_full_validation
    (g : PlanckLikelihoodCompletenessGate)
    (hPolicy :
      Not g.highlTEStandaloneAvailable ->
      Not g.highlEEStandaloneAvailable ->
      Not g.fullPlanckValidationAllowed)
    (hTE : Not g.highlTEStandaloneAvailable)
    (hEE : Not g.highlEEStandaloneAvailable) :
    Not (g.fullPlanckValidationAllowed) := by
  exact hPolicy hTE hEE

end P0EFTJanusZ4PlanckLikelihoodCompletenessGate
end JanusFormal

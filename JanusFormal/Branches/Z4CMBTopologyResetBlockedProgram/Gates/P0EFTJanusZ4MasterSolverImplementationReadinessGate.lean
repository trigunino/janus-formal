import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4MasterSolverProvenanceManifestGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterSolverImplementationReadinessGate

set_option autoImplicit false

structure MasterSolverImplementationReadinessGate where
  solverImplemented : Prop
  internalDiagnosticGenerationReady : Prop
  provenanceReady : Prop
  observedPlanckValidation : Prop
  observedLikelihoodAllowed : Prop
  candidatePromotionAllowed : Prop
  retuningAllowed : Prop
  fullPlanckValidation : Prop

def solverImplementationReady (g : MasterSolverImplementationReadinessGate) : Prop :=
  g.solverImplemented /\
  g.internalDiagnosticGenerationReady /\
  g.provenanceReady /\
  Not g.observedPlanckValidation /\
  Not g.observedLikelihoodAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.retuningAllowed /\
  Not g.fullPlanckValidation

theorem implemented_solver_is_not_planck_validation
    (g : MasterSolverImplementationReadinessGate)
    (h : solverImplementationReady g) :
    g.solverImplemented /\ Not g.observedPlanckValidation /\ Not g.fullPlanckValidation := by
  rcases h with âŸ¨hSolver, _, _, hPlanck, _, _, _, hFullâŸ©
  exact âŸ¨hSolver, hPlanck, hFullâŸ©

end P0EFTJanusZ4MasterSolverImplementationReadinessGate
end JanusFormal

import JanusFormal.P0EFTJanusZ4PhaseKernelApplicationDiagnostic

namespace JanusFormal
namespace P0EFTJanusZ4ParityPolarizationMixer

set_option autoImplicit false

structure ParityPolarizationMixer where
  evenOddDecompositionDeclared : Prop
  holstProjectionDeclared : Prop
  teZeroCrossingsMeasured : Prop
  highlTEShapeMeasured : Prop
  highlEEShapeMeasured : Prop
  eeNormPreserved : Prop
  teRestored : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def diagnosticReady (m : ParityPolarizationMixer) : Prop :=
  m.evenOddDecompositionDeclared /\
  m.holstProjectionDeclared /\
  m.teZeroCrossingsMeasured /\
  m.highlTEShapeMeasured /\
  m.highlEEShapeMeasured

def safeSolverIntegrationReady (m : ParityPolarizationMixer) : Prop :=
  diagnosticReady m /\ m.teRestored /\ m.eeNormPreserved

theorem mixer_diagnostic_does_not_claim_solver_safety
    (m : ParityPolarizationMixer)
    (_h : diagnosticReady m)
    (hEE : Not m.eeNormPreserved) :
    Not (safeSolverIntegrationReady m) := by
  intro h
  exact hEE h.right.right

theorem mixer_keeps_solver_frozen
    (m : ParityPolarizationMixer)
    (_h : diagnosticReady m)
    (hFrozen : Not m.solverNumericsModified) :
    Not m.solverNumericsModified := by
  exact hFrozen

theorem mixer_does_not_claim_planck
    (m : ParityPolarizationMixer)
    (_h : diagnosticReady m)
    (hNoClaim : Not m.planckValidationClaimed) :
    Not m.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4ParityPolarizationMixer
end JanusFormal

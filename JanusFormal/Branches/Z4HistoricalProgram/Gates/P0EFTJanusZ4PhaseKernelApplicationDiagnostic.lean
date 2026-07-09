import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4TightCouplingQuadrupoleIdentity

namespace JanusFormal
namespace P0EFTJanusZ4PhaseKernelApplicationDiagnostic

set_option autoImplicit false

structure PhaseKernelApplicationDiagnostic where
  tightQuadrupoleIdentityApplied : Prop
  baselineSpectrumMeasured : Prop
  tightQuadrupoleSpectrumMeasured : Prop
  tightVisibilitySilkSpectrumMeasured : Prop
  teZeroCrossingsMeasured : Prop
  highlTEShapeMeasured : Prop
  highlTTPeakPhaseMeasured : Prop
  highlEEShapeMeasured : Prop
  integrationVerdictDeclared : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def diagnosticReady (d : PhaseKernelApplicationDiagnostic) : Prop :=
  d.tightQuadrupoleIdentityApplied /\
  d.baselineSpectrumMeasured /\
  d.tightQuadrupoleSpectrumMeasured /\
  d.tightVisibilitySilkSpectrumMeasured /\
  d.teZeroCrossingsMeasured /\
  d.highlTEShapeMeasured /\
  d.highlTTPeakPhaseMeasured /\
  d.highlEEShapeMeasured /\
  d.integrationVerdictDeclared

theorem application_diagnostic_keeps_solver_frozen
    (d : PhaseKernelApplicationDiagnostic)
    (_h : diagnosticReady d)
    (hFrozen : Not d.solverNumericsModified) :
    Not d.solverNumericsModified := by
  exact hFrozen

theorem application_diagnostic_does_not_claim_planck
    (d : PhaseKernelApplicationDiagnostic)
    (_h : diagnosticReady d)
    (hNoClaim : Not d.planckValidationClaimed) :
    Not d.planckValidationClaimed := by
  exact hNoClaim

theorem quadrupole_identity_can_feed_application_diagnostic
    (q : P0EFTJanusZ4TightCouplingQuadrupoleIdentity.TightCouplingQuadrupoleIdentity)
    (d : PhaseKernelApplicationDiagnostic)
    (hq : P0EFTJanusZ4TightCouplingQuadrupoleIdentity.quadrupoleIdentityReady q)
    (hTransport : q.theta2EqualsKVbOverTauDotDerived -> d.tightQuadrupoleIdentityApplied)
    (hRest :
      d.baselineSpectrumMeasured /\
      d.tightQuadrupoleSpectrumMeasured /\
      d.tightVisibilitySilkSpectrumMeasured /\
      d.teZeroCrossingsMeasured /\
      d.highlTEShapeMeasured /\
      d.highlTTPeakPhaseMeasured /\
      d.highlEEShapeMeasured /\
      d.integrationVerdictDeclared) :
    diagnosticReady d := by
  exact And.intro (hTransport hq.right.right.right.right.right.right) hRest

end P0EFTJanusZ4PhaseKernelApplicationDiagnostic
end JanusFormal

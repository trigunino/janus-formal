namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermMinimalBasisDualRouteDecisionGate

set_option autoImplicit false

structure MinimalBasisDualRouteDecisionGate where
  activeRHTraceTargetAvailable : Prop
  activeRKTraceTargetAvailable : Prop
  traceSolutionRouteReady : Prop
  nonzeroParametricECountertermReady : Prop
  coefficientsDetermined : Prop
  numericECountertermReady : Prop
  doNotClaimECountertermZero : Prop
  doNotFitCoefficients : Prop

def activeTraceRouteReady (g : MinimalBasisDualRouteDecisionGate) : Prop :=
  g.activeRHTraceTargetAvailable /\
  g.activeRKTraceTargetAvailable /\
  g.traceSolutionRouteReady /\
  g.coefficientsDetermined

def nonzeroNumericRouteReady (g : MinimalBasisDualRouteDecisionGate) : Prop :=
  g.nonzeroParametricECountertermReady /\
  g.coefficientsDetermined /\
  g.numericECountertermReady

theorem missing_traces_block_trace_solution
    (g : MinimalBasisDualRouteDecisionGate)
    (hMissing : Not g.activeRHTraceTargetAvailable) :
    Not (activeTraceRouteReady g) := by
  intro hReady
  exact hMissing hReady.1

theorem parametric_route_does_not_give_numeric_without_coefficients
    (g : MinimalBasisDualRouteDecisionGate)
    (hMissing : Not g.coefficientsDetermined) :
    Not (nonzeroNumericRouteReady g) := by
  intro hReady
  exact hMissing hReady.2.1

end P0EFTJanusZ2SigmaCountertermMinimalBasisDualRouteDecisionGate
end JanusFormal

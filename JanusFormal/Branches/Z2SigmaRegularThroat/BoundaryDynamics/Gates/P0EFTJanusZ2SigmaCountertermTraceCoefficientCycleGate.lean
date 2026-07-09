namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTraceCoefficientCycleGate

set_option autoImplicit false

structure CountertermTraceCoefficientCycleGate where
  activeSurfaceDensityCoefficientsAvailable : Prop
  activeTraceResidualInputsAvailable : Prop
  alphaRadialComponentsAvailable : Prop
  minimalBasisCoefficientsAvailable : Prop
  directSigmaActionDerivationAvailable : Prop
  residualMatchingRouteAvailable : Prop
  activeRSigmaRadiusSolutionAvailable : Prop
  eCountertermReady : Prop
  fittedCountertermCoefficientsForbidden : Prop
  eCountertermZeroAssumptionForbidden : Prop
  cartanGHYLinearKDuplicateForbidden : Prop

def coefficientRouteReady (g : CountertermTraceCoefficientCycleGate) : Prop :=
  g.activeSurfaceDensityCoefficientsAvailable \/
  g.activeTraceResidualInputsAvailable

def traceRouteReady (g : CountertermTraceCoefficientCycleGate) : Prop :=
  g.activeTraceResidualInputsAvailable /\
  g.residualMatchingRouteAvailable /\
  g.minimalBasisCoefficientsAvailable

def directActionRouteReady (g : CountertermTraceCoefficientCycleGate) : Prop :=
  g.directSigmaActionDerivationAvailable /\
  g.activeSurfaceDensityCoefficientsAvailable

def countertermRadialClosureReady (g : CountertermTraceCoefficientCycleGate) : Prop :=
  (traceRouteReady g \/ directActionRouteReady g) /\
  g.activeRSigmaRadiusSolutionAvailable /\
  g.eCountertermReady /\
  g.fittedCountertermCoefficientsForbidden /\
  g.eCountertermZeroAssumptionForbidden /\
  g.cartanGHYLinearKDuplicateForbidden

theorem coefficient_route_blocked_without_traces_or_direct_coefficients
    (g : CountertermTraceCoefficientCycleGate)
    (hNoCoeff : Not g.activeSurfaceDensityCoefficientsAvailable)
    (hNoTrace : Not g.activeTraceResidualInputsAvailable) :
    Not (coefficientRouteReady g) := by
  intro hReady
  cases hReady with
  | inl hCoeff => exact hNoCoeff hCoeff
  | inr hTrace => exact hNoTrace hTrace

theorem trace_route_requires_trace_inputs
    (g : CountertermTraceCoefficientCycleGate)
    (hReady : traceRouteReady g) :
    g.activeTraceResidualInputsAvailable := by
  exact hReady.1

theorem direct_route_requires_sigma_action_derivation
    (g : CountertermTraceCoefficientCycleGate)
    (hReady : directActionRouteReady g) :
    g.directSigmaActionDerivationAvailable := by
  exact hReady.1

theorem counterterm_closure_blocked_without_trace_or_direct_route
    (g : CountertermTraceCoefficientCycleGate)
    (hNoTrace : Not (traceRouteReady g))
    (hNoDirect : Not (directActionRouteReady g)) :
    Not (countertermRadialClosureReady g) := by
  intro hReady
  cases hReady.1 with
  | inl hTrace => exact hNoTrace hTrace
  | inr hDirect => exact hNoDirect hDirect

theorem e_counterterm_zero_assumption_cannot_close
    (g : CountertermTraceCoefficientCycleGate)
    (_hForbidden : g.eCountertermZeroAssumptionForbidden)
    (hNotReady : Not g.eCountertermReady) :
    Not (countertermRadialClosureReady g) := by
  intro hReady
  exact hNotReady hReady.2.2.1

end P0EFTJanusZ2SigmaCountertermTraceCoefficientCycleGate
end JanusFormal

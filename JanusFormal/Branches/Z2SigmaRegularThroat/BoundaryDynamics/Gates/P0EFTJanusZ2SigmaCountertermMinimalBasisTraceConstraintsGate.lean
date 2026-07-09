namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermMinimalBasisTraceConstraintsGate

set_option autoImplicit false

structure MinimalBasisTraceConstraintsGate where
  minimalBasisImported : Prop
  radialVariationFormulaDeclared : Prop
  kTraceVariationDeclared : Prop
  metricTraceUnderDeterminedDeclared : Prop
  eCountertermZeroToyConstraintAvailable : Prop
  c1ZeroFromToyEZero : Prop
  c2c3RelationFromToyEZero : Prop
  freeParameterRemains : Prop
  formalFiniteRadiusBalanceDeclared : Prop
  formalFiniteRadiusDependsOnCoefficients : Prop
  activeRKTraceTargetAvailable : Prop
  activeRHTraceTargetAvailable : Prop
  coefficientsFullyDetermined : Prop

def toyTraceDiagnosticReady (g : MinimalBasisTraceConstraintsGate) : Prop :=
  g.minimalBasisImported /\
  g.radialVariationFormulaDeclared /\
  g.kTraceVariationDeclared /\
  g.metricTraceUnderDeterminedDeclared /\
  g.eCountertermZeroToyConstraintAvailable /\
  g.c1ZeroFromToyEZero /\
  g.c2c3RelationFromToyEZero /\
  g.freeParameterRemains /\
  g.formalFiniteRadiusBalanceDeclared /\
  g.formalFiniteRadiusDependsOnCoefficients

def coefficientsSolved (g : MinimalBasisTraceConstraintsGate) : Prop :=
  toyTraceDiagnosticReady g /\
  g.activeRKTraceTargetAvailable /\
  g.activeRHTraceTargetAvailable /\
  g.coefficientsFullyDetermined

theorem toy_ezero_leaves_free_parameter
    (g : MinimalBasisTraceConstraintsGate)
    (hReady : toyTraceDiagnosticReady g) :
    g.freeParameterRemains := by
  exact hReady.2.2.2.2.2.2.2.1

theorem formal_radius_still_depends_on_coefficients
    (g : MinimalBasisTraceConstraintsGate)
    (hReady : toyTraceDiagnosticReady g) :
    g.formalFiniteRadiusDependsOnCoefficients := by
  exact hReady.2.2.2.2.2.2.2.2.2

theorem coefficients_not_solved_without_rk_trace
    (g : MinimalBasisTraceConstraintsGate)
    (hMissing : Not g.activeRKTraceTargetAvailable) :
    Not (coefficientsSolved g) := by
  intro hSolved
  exact hMissing hSolved.2.1

theorem coefficients_not_solved_without_rh_trace
    (g : MinimalBasisTraceConstraintsGate)
    (hMissing : Not g.activeRHTraceTargetAvailable) :
    Not (coefficientsSolved g) := by
  intro hSolved
  exact hMissing hSolved.2.2.1

end P0EFTJanusZ2SigmaCountertermMinimalBasisTraceConstraintsGate
end JanusFormal

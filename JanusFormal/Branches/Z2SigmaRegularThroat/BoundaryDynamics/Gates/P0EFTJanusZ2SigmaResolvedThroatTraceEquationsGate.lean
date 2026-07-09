import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaResolvedThroatTraceEquationsGate

set_option autoImplicit false

structure ResolvedThroatTraceEquationsGate where
  lanczosIsraelTraceEquationDeclared : Prop
  z2NormalReversalInserted : Prop
  finiteThroatTraceTargetDerived : Prop
  minimalDensityTraceEquationsDerived : Prop
  rHTraceEquationDerived : Prop
  rKTraceEquationDerived : Prop
  rHTraceValueReady : Prop
  rKTraceValueReady : Prop
  minimalConstantBasisCloses : Prop
  nonMinimalDensityOrMixedEnsembleRequired : Prop
  coefficientFitForbidden : Prop
  eCountertermZeroForced : Prop

def traceEquationsDeclared
    (g : ResolvedThroatTraceEquationsGate) : Prop :=
  g.lanczosIsraelTraceEquationDeclared /\
  g.z2NormalReversalInserted /\
  g.finiteThroatTraceTargetDerived /\
  g.minimalDensityTraceEquationsDerived /\
  g.rHTraceEquationDerived /\
  g.rKTraceEquationDerived /\
  g.coefficientFitForbidden

theorem value_closure_requires_trace_values
    (g : ResolvedThroatTraceEquationsGate)
    (hValues : g.rHTraceValueReady /\ g.rKTraceValueReady) :
    g.rHTraceValueReady /\ g.rKTraceValueReady := by
  exact hValues

theorem minimal_basis_nonclosure_points_to_next_branch
    (g : ResolvedThroatTraceEquationsGate)
    (hEq : traceEquationsDeclared g)
    (hNoClose : Not g.minimalConstantBasisCloses)
    (hNext : traceEquationsDeclared g -> Not g.minimalConstantBasisCloses ->
      g.nonMinimalDensityOrMixedEnsembleRequired) :
    g.nonMinimalDensityOrMixedEnsembleRequired := by
  exact hNext hEq hNoClose

end P0EFTJanusZ2SigmaResolvedThroatTraceEquationsGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermMinimalBasisCoefficientSolverGate

set_option autoImplicit false

structure MinimalBasisCoefficientSolverGate where
  activeRHTraceTargetAvailable : Prop
  activeRKTraceTargetAvailable : Prop
  traceInputsWritten : Prop
  linearSystemDeclared : Prop
  cartanCountertermBalanceIncluded : Prop
  linearKPartitionEnforced : Prop
  c1ZeroAfterPartition : Prop
  fittedCoefficientsForbidden : Prop
  coefficientsSolved : Prop

def coefficientSolverReady (g : MinimalBasisCoefficientSolverGate) : Prop :=
  g.activeRHTraceTargetAvailable /\
  g.activeRKTraceTargetAvailable /\
  g.traceInputsWritten /\
  g.linearSystemDeclared /\
  g.cartanCountertermBalanceIncluded /\
  g.linearKPartitionEnforced /\
  g.c1ZeroAfterPartition /\
  g.fittedCoefficientsForbidden /\
  g.coefficientsSolved

theorem coefficient_solver_requires_active_h_trace
    (g : MinimalBasisCoefficientSolverGate)
    (hReady : coefficientSolverReady g) :
    g.activeRHTraceTargetAvailable := by
  exact hReady.1

theorem coefficient_solver_requires_active_k_trace
    (g : MinimalBasisCoefficientSolverGate)
    (hReady : coefficientSolverReady g) :
    g.activeRKTraceTargetAvailable := by
  exact hReady.2.1

theorem coefficient_solver_enforces_linear_k_partition
    (g : MinimalBasisCoefficientSolverGate)
    (hReady : coefficientSolverReady g) :
    g.c1ZeroAfterPartition := by
  exact hReady.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaCountertermMinimalBasisCoefficientSolverGate
end JanusFormal

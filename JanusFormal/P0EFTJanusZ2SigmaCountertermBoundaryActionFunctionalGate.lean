import JanusFormal.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermBoundaryActionFunctionalGate

set_option autoImplicit false

structure CountertermBoundaryActionFunctionalGate where
  sigmaFullBoundaryActionClosed : Prop
  localDensityBasisLedgerDeclared : Prop
  boundaryActionFunctionalWritten : Prop
  inducedMeasureFixed : Prop
  notDuplicateOfCartanGHYHolstMatter : Prop
  reducedToLocalDensityBasis : Prop
  integrationConstantFixedSymbolically : Prop
  explicitCoefficientExpansionReady : Prop
  densityInputsAllowed : Prop

def boundaryActionFunctionalClosed
    (g : CountertermBoundaryActionFunctionalGate) : Prop :=
  g.sigmaFullBoundaryActionClosed /\
  g.localDensityBasisLedgerDeclared /\
  g.boundaryActionFunctionalWritten /\
  g.inducedMeasureFixed /\
  g.notDuplicateOfCartanGHYHolstMatter /\
  g.reducedToLocalDensityBasis /\
  g.integrationConstantFixedSymbolically

def densityInputsReady
    (g : CountertermBoundaryActionFunctionalGate) : Prop :=
  boundaryActionFunctionalClosed g /\
  g.explicitCoefficientExpansionReady /\
  g.densityInputsAllowed

theorem boundary_action_closure_requires_measure
    (g : CountertermBoundaryActionFunctionalGate)
    (h : boundaryActionFunctionalClosed g) :
    g.inducedMeasureFixed := by
  exact h.2.2.2.1

theorem missing_coefficients_block_density_inputs
    (g : CountertermBoundaryActionFunctionalGate)
    (hMissing : Not g.explicitCoefficientExpansionReady) :
    Not (densityInputsReady g) := by
  intro hReady
  exact hMissing hReady.2.1

end P0EFTJanusZ2SigmaCountertermBoundaryActionFunctionalGate
end JanusFormal

import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermBoundaryActionFunctionalGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermCoefficientExpansionObligationGate

set_option autoImplicit false

structure CountertermCoefficientExpansionObligationGate where
  boundaryActionFunctionalClosed : Prop
  variationalCoefficientFormulaClosed : Prop
  rHAbFromActionVariation : Prop
  rKAbFromActionVariation : Prop
  rChiFromActionVariation : Prop
  rTAClosedOnTorsionlessBranch : Prop
  explicitCoefficientExpansionReady : Prop
  densityInputsAllowed : Prop

def coefficientExpansionReady
    (g : CountertermCoefficientExpansionObligationGate) : Prop :=
  g.boundaryActionFunctionalClosed /\
  g.variationalCoefficientFormulaClosed /\
  g.rHAbFromActionVariation /\
  g.rKAbFromActionVariation /\
  g.rChiFromActionVariation /\
  g.rTAClosedOnTorsionlessBranch /\
  g.explicitCoefficientExpansionReady

theorem missing_metric_coefficient_blocks_density_inputs
    (g : CountertermCoefficientExpansionObligationGate)
    (hMissing : Not g.rHAbFromActionVariation) :
    Not (coefficientExpansionReady g) := by
  intro hReady
  exact hMissing hReady.2.2.1

theorem density_inputs_require_explicit_coefficients
    (g : CountertermCoefficientExpansionObligationGate)
    (hReady : coefficientExpansionReady g) :
    g.explicitCoefficientExpansionReady := by
  exact hReady.2.2.2.2.2.2

end P0EFTJanusZ2SigmaCountertermCoefficientExpansionObligationGate
end JanusFormal

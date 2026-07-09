import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermResidualIntegrabilityGate

set_option autoImplicit false

structure CountertermResidualIntegrabilityGate where
  residualOneFormDecompositionGateDeclared : Prop
  covariantPhaseSpaceBibliographyChecked : Prop
  variationalBicomplexBibliographyChecked : Prop
  fieldSpaceExteriorDerivativeDeclared : Prop
  channelCrossDerivativeMatrixDeclared : Prop
  z2BoundaryCompatibilityDeclared : Prop
  noFittedExactnessCondition : Prop
  residualOneFormComponentsExplicit : Prop
  fieldSpaceCurlComputed : Prop
  channelCrossDerivativesSymmetric : Prop
  z2BoundaryCompatibilityProved : Prop
  residualOneFormExact : Prop
  readyForCountertermPrimitive : Prop

def countertermResidualIntegrabilityLedgerDeclared
    (g : CountertermResidualIntegrabilityGate) : Prop :=
  g.residualOneFormDecompositionGateDeclared /\
  g.covariantPhaseSpaceBibliographyChecked /\
  g.variationalBicomplexBibliographyChecked /\
  g.fieldSpaceExteriorDerivativeDeclared /\
  g.channelCrossDerivativeMatrixDeclared /\
  g.z2BoundaryCompatibilityDeclared /\
  g.noFittedExactnessCondition

def countertermResidualIntegrabilityReady
    (g : CountertermResidualIntegrabilityGate) : Prop :=
  countertermResidualIntegrabilityLedgerDeclared g /\
  g.residualOneFormComponentsExplicit /\
  g.fieldSpaceCurlComputed /\
  g.channelCrossDerivativesSymmetric /\
  g.z2BoundaryCompatibilityProved /\
  g.residualOneFormExact /\
  g.readyForCountertermPrimitive

theorem integrability_ready_requires_exact_residual_one_form
    (g : CountertermResidualIntegrabilityGate)
    (hReady : countertermResidualIntegrabilityReady g) :
    g.residualOneFormExact := by
  exact hReady.right.right.right.right.right.left

end P0EFTJanusZ2SigmaCountertermResidualIntegrabilityGate
end JanusFormal

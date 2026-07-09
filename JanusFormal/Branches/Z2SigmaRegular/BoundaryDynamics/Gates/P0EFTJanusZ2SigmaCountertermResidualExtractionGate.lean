import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGate
import JanusFormal.Branches.Z2SigmaRegular.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermResidualIntegrabilityGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermResidualExtractionGate

set_option autoImplicit false

structure CountertermResidualExtractionGate where
  nonlinearResidualClosureImported : Prop
  localDensityBasisGateDeclared : Prop
  residualOneFormDecompositionGateDeclared : Prop
  residualIntegrabilityGateDeclared : Prop
  boundaryVariationBibliographyChecked : Prop
  residualOneFormDeclared : Prop
  residualIntegrabilityConditionDeclared : Prop
  countertermPrimitiveDeclared : Prop
  uniquenessTransportDeclared : Prop
  observationalFitForbidden : Prop
  residualOneFormExplicit : Prop
  residualIntegrabilityProved : Prop
  countertermPrimitiveIntegrated : Prop
  lCtLocalExpansionDerived : Prop
  lCtReadyForDensityExpansionGate : Prop

def countertermResidualExtractionLedgerDeclared
    (g : CountertermResidualExtractionGate) : Prop :=
  g.nonlinearResidualClosureImported /\
  g.localDensityBasisGateDeclared /\
  g.residualOneFormDecompositionGateDeclared /\
  g.residualIntegrabilityGateDeclared /\
  g.boundaryVariationBibliographyChecked /\
  g.residualOneFormDeclared /\
  g.residualIntegrabilityConditionDeclared /\
  g.countertermPrimitiveDeclared /\
  g.uniquenessTransportDeclared /\
  g.observationalFitForbidden

def countertermResidualExtractionReady
    (g : CountertermResidualExtractionGate) : Prop :=
  countertermResidualExtractionLedgerDeclared g /\
  g.residualOneFormExplicit /\
  g.residualIntegrabilityProved /\
  g.countertermPrimitiveIntegrated /\
  g.lCtLocalExpansionDerived /\
  g.lCtReadyForDensityExpansionGate

theorem residual_extraction_ready_requires_integrated_primitive
    (g : CountertermResidualExtractionGate)
    (hReady : countertermResidualExtractionReady g) :
    g.countertermPrimitiveIntegrated := by
  exact hReady.right.right.right.left

end P0EFTJanusZ2SigmaCountertermResidualExtractionGate
end JanusFormal

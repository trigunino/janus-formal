import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGate

set_option autoImplicit false

structure CountertermResidualOneFormDecompositionGate where
  nonlinearResidualClosureImported : Prop
  localDensityBasisGateDeclared : Prop
  variationalBicomplexBibliographyChecked : Prop
  residualOneFormProblemDeclared : Prop
  activeFieldCoordinatesDeclared : Prop
  tetradResidualChannelGateDeclared : Prop
  connectionResidualChannelGateDeclared : Prop
  spinorResidualChannelGateDeclared : Prop
  embeddingResidualChannelGateDeclared : Prop
  matterFluxResidualChannelGateDeclared : Prop
  tetradResidualChannelDeclared : Prop
  connectionResidualChannelDeclared : Prop
  spinorResidualChannelDeclared : Prop
  embeddingResidualChannelDeclared : Prop
  matterFluxResidualChannelDeclared : Prop
  noFittedResidualCoefficient : Prop
  residualOneFormComponentsExplicit : Prop
  residualOneFormLocalInAllowedBasis : Prop
  residualOneFormReadyForIntegrabilityGate : Prop

def countertermResidualOneFormDecompositionLedgerDeclared
    (g : CountertermResidualOneFormDecompositionGate) : Prop :=
  g.nonlinearResidualClosureImported /\
  g.localDensityBasisGateDeclared /\
  g.variationalBicomplexBibliographyChecked /\
  g.residualOneFormProblemDeclared /\
  g.activeFieldCoordinatesDeclared /\
  g.tetradResidualChannelGateDeclared /\
  g.connectionResidualChannelGateDeclared /\
  g.spinorResidualChannelGateDeclared /\
  g.embeddingResidualChannelGateDeclared /\
  g.matterFluxResidualChannelGateDeclared /\
  g.tetradResidualChannelDeclared /\
  g.connectionResidualChannelDeclared /\
  g.spinorResidualChannelDeclared /\
  g.embeddingResidualChannelDeclared /\
  g.matterFluxResidualChannelDeclared /\
  g.noFittedResidualCoefficient

def countertermResidualOneFormDecompositionReady
    (g : CountertermResidualOneFormDecompositionGate) : Prop :=
  countertermResidualOneFormDecompositionLedgerDeclared g /\
  g.residualOneFormComponentsExplicit /\
  g.residualOneFormLocalInAllowedBasis /\
  g.residualOneFormReadyForIntegrabilityGate

theorem one_form_ready_requires_explicit_components
    (g : CountertermResidualOneFormDecompositionGate)
    (hReady : countertermResidualOneFormDecompositionReady g) :
    g.residualOneFormComponentsExplicit := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGate
end JanusFormal

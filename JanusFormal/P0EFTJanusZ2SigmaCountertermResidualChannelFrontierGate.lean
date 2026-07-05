import JanusFormal.P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGate

set_option autoImplicit false

structure CountertermResidualChannelFrontierGate where
  tetradResidualChannelImported : Prop
  connectionResidualChannelImported : Prop
  spinorResidualChannelImported : Prop
  embeddingResidualChannelImported : Prop
  matterFluxResidualChannelImported : Prop
  variationalBicomplexBibliographyChecked : Prop
  noFittedResidualCoefficient : Prop
  tetradResidualReady : Prop
  connectionResidualReady : Prop
  spinorResidualReady : Prop
  embeddingResidualReady : Prop
  matterFluxResidualReady : Prop
  nearestResidualChannelFrontierDeclared : Prop
  nearestResidualChannelFrontierIsDiagnosticOnly : Prop
  allResidualChannelsExplicit : Prop
  residualOneFormReadyForDecomposition : Prop

def residualChannelFrontierLedgerDeclared
    (g : CountertermResidualChannelFrontierGate) : Prop :=
  g.tetradResidualChannelImported /\
  g.connectionResidualChannelImported /\
  g.spinorResidualChannelImported /\
  g.embeddingResidualChannelImported /\
  g.matterFluxResidualChannelImported /\
  g.variationalBicomplexBibliographyChecked /\
  g.noFittedResidualCoefficient

def residualChannelFrontierReady
    (g : CountertermResidualChannelFrontierGate) : Prop :=
  residualChannelFrontierLedgerDeclared g /\
  g.tetradResidualReady /\
  g.connectionResidualReady /\
  g.spinorResidualReady /\
  g.embeddingResidualReady /\
  g.matterFluxResidualReady /\
  g.nearestResidualChannelFrontierDeclared /\
  g.nearestResidualChannelFrontierIsDiagnosticOnly /\
  g.allResidualChannelsExplicit /\
  g.residualOneFormReadyForDecomposition

theorem residual_frontier_requires_tetrad_channel
    (g : CountertermResidualChannelFrontierGate)
    (hReady : residualChannelFrontierReady g) :
    g.tetradResidualReady := by
  exact hReady.2.1

theorem residual_frontier_feeds_one_form_decomposition
    (g : CountertermResidualChannelFrontierGate)
    (hReady : residualChannelFrontierReady g) :
    g.residualOneFormReadyForDecomposition := by
  exact hReady.2.2.2.2.2.2.2.2.2

theorem nearest_frontier_does_not_close_residual_channels
    (g : CountertermResidualChannelFrontierGate)
    (hNotAll : Not g.allResidualChannelsExplicit) :
    Not (residualChannelFrontierReady g) := by
  intro hReady
  exact hNotAll hReady.2.2.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGate
end JanusFormal

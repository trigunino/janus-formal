import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermResidualExtractionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermDensityExpansionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGate

set_option autoImplicit false

structure CountertermRadialReductionFrontierGate where
  countertermRadialBlockImported : Prop
  residualExtractionGateImported : Prop
  densityExpansionGateImported : Prop
  boundaryCountertermBibliographyChecked : Prop
  reductionChainDeclared : Prop
  noFittedCountertermCoefficient : Prop
  residualOneFormExplicit : Prop
  residualIntegrabilityProved : Prop
  countertermPrimitiveIntegrated : Prop
  lCtLocalExpansionDerived : Prop
  lCtReadyForRadialVariation : Prop
  eCountertermRadialBlockReduced : Prop
  countertermBlockReduced : Prop

def countertermRadialReductionFrontierLedgerDeclared
    (g : CountertermRadialReductionFrontierGate) : Prop :=
  g.countertermRadialBlockImported /\
  g.residualExtractionGateImported /\
  g.densityExpansionGateImported /\
  g.boundaryCountertermBibliographyChecked /\
  g.reductionChainDeclared /\
  g.noFittedCountertermCoefficient

def countertermRadialReductionReady
    (g : CountertermRadialReductionFrontierGate) : Prop :=
  countertermRadialReductionFrontierLedgerDeclared g /\
  g.residualOneFormExplicit /\
  g.residualIntegrabilityProved /\
  g.countertermPrimitiveIntegrated /\
  g.lCtLocalExpansionDerived /\
  g.lCtReadyForRadialVariation /\
  g.eCountertermRadialBlockReduced /\
  g.countertermBlockReduced

theorem counterterm_reduction_requires_integrated_primitive
    (g : CountertermRadialReductionFrontierGate)
    (hReady : countertermRadialReductionReady g) :
    g.countertermPrimitiveIntegrated := by
  exact hReady.2.2.2.1

theorem counterterm_reduction_feeds_radius_frontier
    (g : CountertermRadialReductionFrontierGate)
    (hReady : countertermRadialReductionReady g) :
    g.countertermBlockReduced := by
  exact hReady.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGate
end JanusFormal

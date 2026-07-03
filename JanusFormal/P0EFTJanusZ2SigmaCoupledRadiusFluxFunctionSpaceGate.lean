import JanusFormal.P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoupledRadiusFluxFunctionSpaceGate

set_option autoImplicit false

structure CoupledRadiusFluxFunctionSpaceGate where
  wellPosednessGateImported : Prop
  thinShellRegularityBibliographyChecked : Prop
  rSigmaDomainDeclared : Prop
  fluxDomainDeclared : Prop
  embeddingTraceDomainDeclared : Prop
  boundaryDataSpaceDeclared : Prop
  gaugeSliceDeclared : Prop
  equationMapDomainCodomainDeclared : Prop
  noDistributionalProductAmbiguityDeclared : Prop
  noObservationalNormFit : Prop
  fluxFunctionalWellDefined : Prop
  embeddingTraceMapContinuous : Prop
  equationMapContinuous : Prop
  linearizedMapFredholmOrInvertible : Prop
  functionSpaceReadyForWellPosedness : Prop

def functionSpaceLedgerDeclared
    (g : CoupledRadiusFluxFunctionSpaceGate) : Prop :=
  g.wellPosednessGateImported /\
  g.thinShellRegularityBibliographyChecked /\
  g.rSigmaDomainDeclared /\
  g.fluxDomainDeclared /\
  g.embeddingTraceDomainDeclared /\
  g.boundaryDataSpaceDeclared /\
  g.gaugeSliceDeclared /\
  g.equationMapDomainCodomainDeclared /\
  g.noDistributionalProductAmbiguityDeclared /\
  g.noObservationalNormFit

def functionSpaceReady
    (g : CoupledRadiusFluxFunctionSpaceGate) : Prop :=
  functionSpaceLedgerDeclared g /\
  g.fluxFunctionalWellDefined /\
  g.embeddingTraceMapContinuous /\
  g.equationMapContinuous /\
  g.linearizedMapFredholmOrInvertible /\
  g.functionSpaceReadyForWellPosedness

theorem function_space_ready_requires_flux_functional
    (g : CoupledRadiusFluxFunctionSpaceGate)
    (hReady : functionSpaceReady g) :
    g.fluxFunctionalWellDefined := by
  exact hReady.2.1

theorem function_space_ready_feeds_well_posedness_frontier
    (g : CoupledRadiusFluxFunctionSpaceGate)
    (hReady : functionSpaceReady g) :
    g.functionSpaceReadyForWellPosedness := by
  exact hReady.2.2.2.2.2

end P0EFTJanusZ2SigmaCoupledRadiusFluxFunctionSpaceGate
end JanusFormal

import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGate

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
  sobolevThresholdTransportImported : Prop
  embeddingFrameTraceTransportImported : Prop
  traceThresholdPassed : Prop
  productThresholdPassed : Prop
  embeddingTraceMapContinuous : Prop
  normalTraceMapContinuous : Prop
  fluxFunctionalWellDefined : Prop
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
  g.noObservationalNormFit /\
  g.sobolevThresholdTransportImported /\
  g.embeddingFrameTraceTransportImported

def functionSpaceReady
    (g : CoupledRadiusFluxFunctionSpaceGate) : Prop :=
  functionSpaceLedgerDeclared g /\
  g.traceThresholdPassed /\
  g.productThresholdPassed /\
  g.embeddingTraceMapContinuous /\
  g.normalTraceMapContinuous /\
  g.fluxFunctionalWellDefined /\
  g.equationMapContinuous /\
  g.linearizedMapFredholmOrInvertible /\
  g.functionSpaceReadyForWellPosedness

theorem function_space_ready_requires_flux_functional
    (g : CoupledRadiusFluxFunctionSpaceGate)
    (hReady : functionSpaceReady g) :
    g.fluxFunctionalWellDefined := by
  rcases hReady with ⟨_, _, _, _, _, hFlux, _, _, _⟩
  exact hFlux

theorem function_space_ready_feeds_well_posedness_frontier
    (g : CoupledRadiusFluxFunctionSpaceGate)
    (hReady : functionSpaceReady g) :
    g.functionSpaceReadyForWellPosedness := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, hReadyForWellPosedness⟩
  exact hReadyForWellPosedness

theorem function_space_ready_requires_frame_traces
    (g : CoupledRadiusFluxFunctionSpaceGate)
    (hReady : functionSpaceReady g) :
    g.embeddingTraceMapContinuous /\ g.normalTraceMapContinuous := by
  rcases hReady with ⟨_, _, _, hEmbedding, hNormal, _, _, _, _⟩
  exact ⟨hEmbedding, hNormal⟩

end P0EFTJanusZ2SigmaCoupledRadiusFluxFunctionSpaceGate
end JanusFormal

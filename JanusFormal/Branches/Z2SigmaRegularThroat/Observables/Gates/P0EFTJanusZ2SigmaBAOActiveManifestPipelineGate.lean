import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaBAOManifestSchemaGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOActiveManifestPipelineGate

set_option autoImplicit false

structure Z2SigmaBAOActiveManifestPipelineGate where
  componentManifestAvailable : Prop
  componentManifestActiveDerived : Prop
  componentManifestNoForbiddenReuse : Prop
  effectiveFluidComponentsAvailable : Prop
  earlyPlasmaComponentsAvailable : Prop
  hZ2SigmaConstructed : Prop
  csZ2SigmaConstructed : Prop
  zdZ2SigmaSolved : Prop
  baoInputManifestWritten : Prop
  sourceComponentManifestHashWritten : Prop
  pipelineGatePassed : Prop

def activeManifestPipelineClosed
    (g : Z2SigmaBAOActiveManifestPipelineGate) : Prop :=
  g.componentManifestAvailable /\
  g.componentManifestActiveDerived /\
  g.componentManifestNoForbiddenReuse /\
  g.effectiveFluidComponentsAvailable /\
  g.earlyPlasmaComponentsAvailable /\
  g.hZ2SigmaConstructed /\
  g.csZ2SigmaConstructed /\
  g.zdZ2SigmaSolved /\
  g.baoInputManifestWritten /\
  g.sourceComponentManifestHashWritten

theorem pipeline_requires_effective_fluid_components
    (g : Z2SigmaBAOActiveManifestPipelineGate)
    (hGate : g.pipelineGatePassed)
    (hImplies : g.pipelineGatePassed -> activeManifestPipelineClosed g) :
    g.effectiveFluidComponentsAvailable := by
  exact (hImplies hGate).2.2.2.1

theorem pipeline_writes_bao_manifest
    (g : Z2SigmaBAOActiveManifestPipelineGate)
    (hClosed : activeManifestPipelineClosed g) :
    g.baoInputManifestWritten := by
  exact hClosed.2.2.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaBAOActiveManifestPipelineGate
end JanusFormal

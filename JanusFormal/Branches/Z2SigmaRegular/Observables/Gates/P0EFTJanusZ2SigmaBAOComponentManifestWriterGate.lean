namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOComponentManifestWriterGate

set_option autoImplicit false

structure Z2SigmaBAOComponentManifestWriterGate where
  strictComponentManifestWriterReady : Prop
  writerRequiresAllActiveComponentFunctions : Prop
  writerRequiresComponentProvenance : Prop
  writerRejectsForbiddenProvenanceTokens : Prop
  writerProducesOfficialPipelineCompatibleSchema : Prop
  officialComponentManifestWritten : Prop

def strictWriterReady
    (g : Z2SigmaBAOComponentManifestWriterGate) : Prop :=
  g.strictComponentManifestWriterReady /\
  g.writerRequiresAllActiveComponentFunctions /\
  g.writerRequiresComponentProvenance /\
  g.writerRejectsForbiddenProvenanceTokens /\
  g.writerProducesOfficialPipelineCompatibleSchema

theorem official_manifest_requires_active_functions
    (g : Z2SigmaBAOComponentManifestWriterGate)
    (hWritten : g.officialComponentManifestWritten)
    (hImplies :
      g.officialComponentManifestWritten -> g.writerRequiresAllActiveComponentFunctions) :
    g.writerRequiresAllActiveComponentFunctions := by
  exact hImplies hWritten

end P0EFTJanusZ2SigmaBAOComponentManifestWriterGate
end JanusFormal

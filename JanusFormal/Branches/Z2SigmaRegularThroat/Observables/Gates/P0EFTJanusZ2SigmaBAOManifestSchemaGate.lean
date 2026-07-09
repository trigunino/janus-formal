import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaBAOOfficialChi2Gate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOManifestSchemaGate

set_option autoImplicit false

structure Z2SigmaBAOManifestSchemaGate where
  schemaDeclared : Prop
  writerReady : Prop
  loaderValidationReady : Prop
  activeCoreZ2SigmaRequired : Prop
  activeDerivedSourceRequired : Prop
  compressedPlanckLCDMRdForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  inputProvenanceRequired : Prop
  sourceComponentManifestPathRequired : Prop
  sourceComponentManifestHashRequired : Prop
  officialChi2RequiresManifest : Prop
  manifestSchemaGatePassed : Prop

def manifestSchemaClosed
    (g : Z2SigmaBAOManifestSchemaGate) : Prop :=
  g.schemaDeclared /\
  g.writerReady /\
  g.loaderValidationReady /\
  g.activeCoreZ2SigmaRequired /\
  g.activeDerivedSourceRequired /\
  g.compressedPlanckLCDMRdForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.inputProvenanceRequired /\
  g.sourceComponentManifestPathRequired /\
  g.sourceComponentManifestHashRequired /\
  g.officialChi2RequiresManifest

theorem manifest_schema_gate_requires_writer
    (g : Z2SigmaBAOManifestSchemaGate)
    (hGate : g.manifestSchemaGatePassed)
    (hImplies : g.manifestSchemaGatePassed -> manifestSchemaClosed g) :
    g.writerReady := by
  exact (hImplies hGate).2.1

end P0EFTJanusZ2SigmaBAOManifestSchemaGate
end JanusFormal

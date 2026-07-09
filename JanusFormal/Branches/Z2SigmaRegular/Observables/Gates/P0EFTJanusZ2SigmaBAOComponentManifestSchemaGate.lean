import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaBAOActiveManifestPipelineGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOComponentManifestSchemaGate

set_option autoImplicit false

structure Z2SigmaBAOComponentManifestSchemaGate where
  schemaDeclared : Prop
  templateDocumentationOnly : Prop
  activeCoreZ2SigmaRequired : Prop
  activeDerivedSourceRequired : Prop
  forbiddenReuseFlagsRequiredFalse : Prop
  flrwComponentFieldsDeclared : Prop
  earlyPlasmaFieldsDeclared : Prop
  componentProvenanceRequired : Prop
  forbiddenComponentProvenanceTokensDeclared : Prop
  componentManifestSchemaGatePassed : Prop

def componentManifestSchemaClosed
    (g : Z2SigmaBAOComponentManifestSchemaGate) : Prop :=
  g.schemaDeclared /\
  g.templateDocumentationOnly /\
  g.activeCoreZ2SigmaRequired /\
  g.activeDerivedSourceRequired /\
  g.forbiddenReuseFlagsRequiredFalse /\
  g.flrwComponentFieldsDeclared /\
  g.earlyPlasmaFieldsDeclared /\
  g.componentProvenanceRequired /\
  g.forbiddenComponentProvenanceTokensDeclared

theorem component_schema_requires_active_source
    (g : Z2SigmaBAOComponentManifestSchemaGate)
    (hGate : g.componentManifestSchemaGatePassed)
    (hImplies : g.componentManifestSchemaGatePassed -> componentManifestSchemaClosed g) :
    g.activeDerivedSourceRequired := by
  exact (hImplies hGate).2.2.2.1

end P0EFTJanusZ2SigmaBAOComponentManifestSchemaGate
end JanusFormal

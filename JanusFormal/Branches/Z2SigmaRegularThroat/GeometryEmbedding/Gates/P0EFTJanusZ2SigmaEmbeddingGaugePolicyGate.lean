import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusLawGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEmbeddingGaugePolicyGate

set_option autoImplicit false

structure EmbeddingGaugePolicyGate where
  thinShellProperTimeBibliographyChecked : Prop
  shellProperTimeGaugeDeclared : Prop
  radialEmbeddingGaugeDeclared : Prop
  gaugeDoesNotFixThroatRadiusDeclared : Prop
  observationalGaugeFitForbidden : Prop
  z2EquivariantGaugeCompatibilityDeclared : Prop
  gaugeFixingEquationsReady : Prop
  gaugeFixesRedundantEmbeddingFunctions : Prop
  gaugePlusThroatLawDeterminesXpm : Prop

def embeddingGaugePolicyDeclared
    (g : EmbeddingGaugePolicyGate) : Prop :=
  g.thinShellProperTimeBibliographyChecked /\
  g.shellProperTimeGaugeDeclared /\
  g.radialEmbeddingGaugeDeclared /\
  g.gaugeDoesNotFixThroatRadiusDeclared /\
  g.observationalGaugeFitForbidden /\
  g.z2EquivariantGaugeCompatibilityDeclared

def embeddingGaugeClosureReady
    (g : EmbeddingGaugePolicyGate) : Prop :=
  embeddingGaugePolicyDeclared g /\
  g.gaugeFixingEquationsReady /\
  g.gaugeFixesRedundantEmbeddingFunctions /\
  g.gaugePlusThroatLawDeterminesXpm

theorem gauge_closure_does_not_replace_throat_law
    (g : EmbeddingGaugePolicyGate)
    (hPolicy : embeddingGaugePolicyDeclared g) :
    g.gaugeDoesNotFixThroatRadiusDeclared := by
  exact hPolicy.2.2.2.1

end P0EFTJanusZ2SigmaEmbeddingGaugePolicyGate
end JanusFormal

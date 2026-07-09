import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaEmbeddingGaugePolicyGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate

set_option autoImplicit false

structure EmbeddingGaugeEquationGate where
  thinShellInducedMetricBibliographyChecked : Prop
  shellProperTimeGaugeAvailable : Prop
  radialGaugeAvailable : Prop
  inducedMetricNormalizationEquationDeclared : Prop
  tPlusPrimeEquationDeclared : Prop
  tMinusPrimeEquationDeclared : Prop
  z2EquivariantTimeGaugeDeclared : Prop
  observationalGaugeFitForbidden : Prop
  gaugeFixingEquationsReady : Prop
  gaugeFixesRedundantEmbeddingFunctions : Prop
  throatRadiusLawStillRequired : Prop
  xPlusMinusOfADetermined : Prop

def embeddingGaugeEquationsDeclared
    (g : EmbeddingGaugeEquationGate) : Prop :=
  g.thinShellInducedMetricBibliographyChecked /\
  g.shellProperTimeGaugeAvailable /\
  g.radialGaugeAvailable /\
  g.inducedMetricNormalizationEquationDeclared /\
  g.tPlusPrimeEquationDeclared /\
  g.tMinusPrimeEquationDeclared /\
  g.z2EquivariantTimeGaugeDeclared /\
  g.observationalGaugeFitForbidden

def embeddingGaugeEquationsReady
    (g : EmbeddingGaugeEquationGate) : Prop :=
  embeddingGaugeEquationsDeclared g /\
  g.gaugeFixingEquationsReady /\
  g.gaugeFixesRedundantEmbeddingFunctions /\
  g.throatRadiusLawStillRequired

def embeddingGaugeFullClosureReady
    (g : EmbeddingGaugeEquationGate) : Prop :=
  embeddingGaugeEquationsReady g /\
  g.xPlusMinusOfADetermined

theorem gauge_equations_do_not_derive_throat_radius
    (g : EmbeddingGaugeEquationGate)
    (hReady : embeddingGaugeEquationsReady g) :
    g.throatRadiusLawStillRequired := by
  exact hReady.2.2.2

theorem full_embedding_closure_requires_xpm_determined
    (g : EmbeddingGaugeEquationGate)
    (hFull : embeddingGaugeFullClosureReady g) :
    g.xPlusMinusOfADetermined := by
  exact hFull.2

end P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate
end JanusFormal

import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYRadialBlockGate

set_option autoImplicit false

structure CartanGHYRadialBlockGate where
  ghyBrownYorkBibliographyChecked : Prop
  cartanGHYBoundaryTermAvailable : Prop
  radialEmbeddingVariationDeclared : Prop
  inducedMetricRadialVariationDeclared : Prop
  extrinsicCurvatureRadialVariationDeclared : Prop
  z2NormalOrientationDeclared : Prop
  observationalFitForbidden : Prop
  eCartanGHYFunctionalDerivativeDeclared : Prop
  eCartanGHYStructuralReductionReady : Prop
  eCartanGHYSymbolicRBlockReady : Prop
  eCartanGHYOfAReady : Prop
  rSigmaOfARequired : Prop

def cartanGHYRadialLedgerDeclared
    (g : CartanGHYRadialBlockGate) : Prop :=
  g.ghyBrownYorkBibliographyChecked /\
  g.cartanGHYBoundaryTermAvailable /\
  g.radialEmbeddingVariationDeclared /\
  g.inducedMetricRadialVariationDeclared /\
  g.extrinsicCurvatureRadialVariationDeclared /\
  g.z2NormalOrientationDeclared /\
  g.observationalFitForbidden /\
  g.eCartanGHYFunctionalDerivativeDeclared

def cartanGHYRadialBlockReduced
    (g : CartanGHYRadialBlockGate) : Prop :=
  cartanGHYRadialLedgerDeclared g /\
  g.eCartanGHYStructuralReductionReady

def cartanGHYSymbolicRBlockReady
    (g : CartanGHYRadialBlockGate) : Prop :=
  cartanGHYRadialBlockReduced g /\
  g.eCartanGHYSymbolicRBlockReady

def cartanGHYRadialBlockOfAReady
    (g : CartanGHYRadialBlockGate) : Prop :=
  cartanGHYRadialBlockReduced g /\
  g.eCartanGHYOfAReady /\
  g.rSigmaOfARequired

theorem cartan_ghy_of_a_requires_radius_law
    (g : CartanGHYRadialBlockGate)
    (hReady : cartanGHYRadialBlockOfAReady g) :
    g.rSigmaOfARequired := by
  exact hReady.2.2

theorem symbolic_R_block_does_not_close_radius_law
    (g : CartanGHYRadialBlockGate)
    (hReady : cartanGHYSymbolicRBlockReady g) :
    g.eCartanGHYSymbolicRBlockReady := by
  exact hReady.2

end P0EFTJanusZ2SigmaCartanGHYRadialBlockGate
end JanusFormal

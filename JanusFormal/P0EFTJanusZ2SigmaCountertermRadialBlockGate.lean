import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermRadialBlockGate

set_option autoImplicit false

structure CountertermRadialBlockGate where
  boundaryCountertermBibliographyChecked : Prop
  sigmaCountertermUniquenessImported : Prop
  countertermCancelsNonlinearResidualImported : Prop
  countertermDensityDeclared : Prop
  radialCountertermVariationDeclared : Prop
  z2OrientationSignDeclared : Prop
  observationalFitForbidden : Prop
  eCountertermFunctionalDerivativeDeclared : Prop
  explicitCountertermDensityReady : Prop
  eCountertermRadialBlockReduced : Prop
  eCountertermOfAReady : Prop

def countertermRadialLedgerDeclared
    (g : CountertermRadialBlockGate) : Prop :=
  g.boundaryCountertermBibliographyChecked /\
  g.sigmaCountertermUniquenessImported /\
  g.countertermCancelsNonlinearResidualImported /\
  g.countertermDensityDeclared /\
  g.radialCountertermVariationDeclared /\
  g.z2OrientationSignDeclared /\
  g.observationalFitForbidden /\
  g.eCountertermFunctionalDerivativeDeclared

def countertermRadialBlockReduced
    (g : CountertermRadialBlockGate) : Prop :=
  countertermRadialLedgerDeclared g /\
  g.explicitCountertermDensityReady /\
  g.eCountertermRadialBlockReduced

def countertermRadialBlockOfAReady
    (g : CountertermRadialBlockGate) : Prop :=
  countertermRadialBlockReduced g /\
  g.eCountertermOfAReady

theorem counterterm_reduction_requires_explicit_density
    (g : CountertermRadialBlockGate)
    (hReady : countertermRadialBlockReduced g) :
    g.explicitCountertermDensityReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaCountertermRadialBlockGate
end JanusFormal

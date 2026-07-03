import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate

set_option autoImplicit false

structure ThroatRadiusBlockExpansionGate where
  israelShellBibliographyChecked : Prop
  ghyBrownYorkBibliographyChecked : Prop
  radialEquationDeclared : Prop
  cartanGHYRadialBlockDeclared : Prop
  holstNiehYanRadialBlockDeclared : Prop
  matterFluxRadialBlockDeclared : Prop
  tunnelJunctionRadialBlockDeclared : Prop
  countertermRadialBlockDeclared : Prop
  noObservationalRadiusFit : Prop
  eRSigmaBlockSumDeclared : Prop
  cartanGHYRadialBlockReduced : Prop
  holstNiehYanRadialBlockReduced : Prop
  matterFluxRadialBlockReduced : Prop
  tunnelJunctionRadialBlockReduced : Prop
  countertermRadialBlockReduced : Prop
  eRSigmaExpanded : Prop
  eRSigmaSolved : Prop
  rSigmaOfAReady : Prop

def throatRadiusBlockLedgerDeclared
    (g : ThroatRadiusBlockExpansionGate) : Prop :=
  g.israelShellBibliographyChecked /\
  g.ghyBrownYorkBibliographyChecked /\
  g.radialEquationDeclared /\
  g.cartanGHYRadialBlockDeclared /\
  g.holstNiehYanRadialBlockDeclared /\
  g.matterFluxRadialBlockDeclared /\
  g.tunnelJunctionRadialBlockDeclared /\
  g.countertermRadialBlockDeclared /\
  g.noObservationalRadiusFit /\
  g.eRSigmaBlockSumDeclared

def allRadialBlocksReduced
    (g : ThroatRadiusBlockExpansionGate) : Prop :=
  g.cartanGHYRadialBlockReduced /\
  g.holstNiehYanRadialBlockReduced /\
  g.matterFluxRadialBlockReduced /\
  g.tunnelJunctionRadialBlockReduced /\
  g.countertermRadialBlockReduced

def throatRadiusBlockExpansionReady
    (g : ThroatRadiusBlockExpansionGate) : Prop :=
  throatRadiusBlockLedgerDeclared g /\
  allRadialBlocksReduced g /\
  g.eRSigmaExpanded

def throatRadiusSolvedFromBlocks
    (g : ThroatRadiusBlockExpansionGate) : Prop :=
  throatRadiusBlockExpansionReady g /\
  g.eRSigmaSolved /\
  g.rSigmaOfAReady

theorem block_expansion_requires_all_radial_blocks
    (g : ThroatRadiusBlockExpansionGate)
    (hReady : throatRadiusBlockExpansionReady g) :
    allRadialBlocksReduced g := by
  exact hReady.2.1

theorem radius_solution_requires_expanded_equation
    (g : ThroatRadiusBlockExpansionGate)
    (hSolved : throatRadiusSolvedFromBlocks g) :
    g.eRSigmaExpanded := by
  exact hSolved.1.2.2

end P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate
end JanusFormal

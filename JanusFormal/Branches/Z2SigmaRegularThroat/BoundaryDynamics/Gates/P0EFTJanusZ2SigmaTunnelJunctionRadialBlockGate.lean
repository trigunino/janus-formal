import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTunnelJunctionRadialBlockGate

set_option autoImplicit false

structure TunnelJunctionRadialBlockGate where
  lanczosIsraelBibliographyChecked : Prop
  extrinsicCurvatureJumpDeclared : Prop
  z2NormalOrientationDeclared : Prop
  radialJunctionVariationDeclared : Prop
  traceReversedSurfaceEquationDeclared : Prop
  nonCircularPartitionGuardDeclared : Prop
  observationalFitForbidden : Prop
  eTunnelJunctionFunctionalDerivativeDeclared : Prop
  eTunnelJunctionStructuralReductionReady : Prop
  deltaKOfAReady : Prop
  eTunnelJunctionOfAReady : Prop

def tunnelJunctionRadialLedgerDeclared
    (g : TunnelJunctionRadialBlockGate) : Prop :=
  g.lanczosIsraelBibliographyChecked /\
  g.extrinsicCurvatureJumpDeclared /\
  g.z2NormalOrientationDeclared /\
  g.radialJunctionVariationDeclared /\
  g.traceReversedSurfaceEquationDeclared /\
  g.nonCircularPartitionGuardDeclared /\
  g.observationalFitForbidden /\
  g.eTunnelJunctionFunctionalDerivativeDeclared

def tunnelJunctionRadialBlockReduced
    (g : TunnelJunctionRadialBlockGate) : Prop :=
  tunnelJunctionRadialLedgerDeclared g /\
  g.eTunnelJunctionStructuralReductionReady

def tunnelJunctionRadialBlockOfAReady
    (g : TunnelJunctionRadialBlockGate) : Prop :=
  tunnelJunctionRadialBlockReduced g /\
  g.deltaKOfAReady /\
  g.eTunnelJunctionOfAReady

theorem tunnel_junction_of_a_requires_deltaK_of_a
    (g : TunnelJunctionRadialBlockGate)
    (hReady : tunnelJunctionRadialBlockOfAReady g) :
    g.deltaKOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaTunnelJunctionRadialBlockGate
end JanusFormal

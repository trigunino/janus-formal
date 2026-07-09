import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermDensityExpansionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaThroatRadiusBlockDependencyAuditGate

set_option autoImplicit false

structure ThroatRadiusBlockDependencyAuditGate where
  throatRadiusBlockExpansionGateDeclared : Prop
  matterFluxRadialBlockGateDeclared : Prop
  countertermRadialBlockGateDeclared : Prop
  countertermDensityExpansionGateDeclared : Prop
  cartanGHYBlockReduced : Prop
  holstNiehYanBlockReduced : Prop
  tunnelJunctionBlockReduced : Prop
  matterFluxBlockReduced : Prop
  countertermBlockReduced : Prop
  eRSigmaExpansionAllowed : Prop
  rSigmaSolutionAllowed : Prop

def throatRadiusBlockDependenciesDeclared
    (g : ThroatRadiusBlockDependencyAuditGate) : Prop :=
  g.throatRadiusBlockExpansionGateDeclared /\
  g.matterFluxRadialBlockGateDeclared /\
  g.countertermRadialBlockGateDeclared /\
  g.countertermDensityExpansionGateDeclared

def missingRadiusBlocksClosed
    (g : ThroatRadiusBlockDependencyAuditGate) : Prop :=
  g.matterFluxBlockReduced /\
  g.countertermBlockReduced

def throatRadiusBlockDependencyReady
    (g : ThroatRadiusBlockDependencyAuditGate) : Prop :=
  throatRadiusBlockDependenciesDeclared g /\
  g.cartanGHYBlockReduced /\
  g.holstNiehYanBlockReduced /\
  g.tunnelJunctionBlockReduced /\
  missingRadiusBlocksClosed g /\
  g.eRSigmaExpansionAllowed /\
  g.rSigmaSolutionAllowed

theorem radius_dependency_ready_requires_missing_blocks
    (g : ThroatRadiusBlockDependencyAuditGate)
    (hReady : throatRadiusBlockDependencyReady g) :
    missingRadiusBlocksClosed g := by
  exact hReady.right.right.right.right.left

end P0EFTJanusZ2SigmaThroatRadiusBlockDependencyAuditGate
end JanusFormal

namespace JanusFormal
namespace P0EFTJanusConformalEinstein00RadiationOmegaRouteGate

set_option autoImplicit false

structure ConformalEinstein00RadiationOmegaRouteGate where
  GPlusWeylKinematicsAvailable : Prop
  Friedmann00ProjectionDeclared : Prop
  RadiationSourceVisibleIn00 : Prop
  BaryonSourceVisibleIn00 : Prop
  NegativeSectorEffectiveSourceVisibleIn00 : Prop
  HatHInputDerived : Prop
  RhoEffPlusDerived : Prop
  OmegaBoundaryConditionDerived : Prop

def ProjectionChoiceClosed
    (g : ConformalEinstein00RadiationOmegaRouteGate) : Prop :=
  g.GPlusWeylKinematicsAvailable /\
  g.Friedmann00ProjectionDeclared /\
  g.RadiationSourceVisibleIn00 /\
  g.BaryonSourceVisibleIn00 /\
  g.NegativeSectorEffectiveSourceVisibleIn00

def Omega00SolutionClosed
    (g : ConformalEinstein00RadiationOmegaRouteGate) : Prop :=
  ProjectionChoiceClosed g /\
  g.HatHInputDerived /\
  g.RhoEffPlusDerived /\
  g.OmegaBoundaryConditionDerived

def Omega00Frontier
    (g : ConformalEinstein00RadiationOmegaRouteGate) : Prop :=
  ProjectionChoiceClosed g /\
  Not g.HatHInputDerived /\
  Not g.RhoEffPlusDerived /\
  Not g.OmegaBoundaryConditionDerived

theorem omega_00_route_needs_background_source_boundary
    (g : ConformalEinstein00RadiationOmegaRouteGate)
    (hFrontier : Omega00Frontier g) :
    Not (Omega00SolutionClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusConformalEinstein00RadiationOmegaRouteGate
end JanusFormal

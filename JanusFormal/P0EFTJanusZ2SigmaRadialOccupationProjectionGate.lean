import JanusFormal.P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaRadialOccupationProjectionGate

set_option autoImplicit false

structure RadialOccupationProjectionGate where
  equivariantProjectionBibliographyChecked : Prop
  fermiDiracIsotropyGateDeclared : Prop
  z2SigmaProjectionMapDeclared : Prop
  rotationEquivarianceCriterionDeclared : Prop
  plusRadialOccupationDeclared : Prop
  minusRadialOccupationDeclared : Prop
  projectedRadialOccupationDeclared : Prop
  observationalFitForbidden : Prop
  plusRadialOccupationReady : Prop
  minusRadialOccupationReady : Prop
  z2SigmaProjectionMapDerived : Prop
  projectionRotationEquivariantDerived : Prop
  projectedRadialOccupationDerived : Prop
  radialOccupationProjectionReady : Prop

def radialOccupationProjectionLedgerDeclared
    (g : RadialOccupationProjectionGate) : Prop :=
  g.equivariantProjectionBibliographyChecked /\
  g.fermiDiracIsotropyGateDeclared /\
  g.z2SigmaProjectionMapDeclared /\
  g.rotationEquivarianceCriterionDeclared /\
  g.plusRadialOccupationDeclared /\
  g.minusRadialOccupationDeclared /\
  g.projectedRadialOccupationDeclared /\
  g.observationalFitForbidden

def radialOccupationProjectionReady
    (g : RadialOccupationProjectionGate) : Prop :=
  radialOccupationProjectionLedgerDeclared g /\
  g.plusRadialOccupationReady /\
  g.minusRadialOccupationReady /\
  g.z2SigmaProjectionMapDerived /\
  g.projectionRotationEquivariantDerived /\
  g.projectedRadialOccupationDerived /\
  g.radialOccupationProjectionReady

theorem radial_projection_requires_equivariance
    (g : RadialOccupationProjectionGate)
    (hReady : radialOccupationProjectionReady g) :
    g.projectionRotationEquivariantDerived := by
  rcases hReady with ⟨_, _, _, _, hEquivariant, _, _⟩
  exact hEquivariant

theorem radial_projection_supplies_projected_radial_occupation
    (g : RadialOccupationProjectionGate)
    (hReady : radialOccupationProjectionReady g) :
    g.projectedRadialOccupationDerived := by
  rcases hReady with ⟨_, _, _, _, _, hProjectedRadial, _⟩
  exact hProjectedRadial

end P0EFTJanusZ2SigmaRadialOccupationProjectionGate
end JanusFormal

import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaProjectedDiracActionReductionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate

set_option autoImplicit false

structure ProjectedDiracMatterCurrentGate where
  diracNoetherCurrentBibliographyChecked : Prop
  projectedDiracActionReductionGateDeclared : Prop
  u1VectorSymmetryDeclared : Prop
  plusCurrentFormulaDeclared : Prop
  minusCurrentFormulaDeclared : Prop
  z2ProjectedCurrentDeclared : Prop
  covariantConservationGuardDeclared : Prop
  observationalFitForbidden : Prop
  projectedDiracActionReady : Prop
  plusCurrentReady : Prop
  minusCurrentReady : Prop
  z2ProjectedCurrentReady : Prop
  plusMinusMatterCurrentsReady : Prop

def projectedDiracMatterCurrentLedgerDeclared
    (g : ProjectedDiracMatterCurrentGate) : Prop :=
  g.diracNoetherCurrentBibliographyChecked /\
  g.projectedDiracActionReductionGateDeclared /\
  g.u1VectorSymmetryDeclared /\
  g.plusCurrentFormulaDeclared /\
  g.minusCurrentFormulaDeclared /\
  g.z2ProjectedCurrentDeclared /\
  g.covariantConservationGuardDeclared /\
  g.observationalFitForbidden

def projectedDiracMatterCurrentReady
    (g : ProjectedDiracMatterCurrentGate) : Prop :=
  projectedDiracMatterCurrentLedgerDeclared g /\
  g.projectedDiracActionReady /\
  g.plusCurrentReady /\
  g.minusCurrentReady /\
  g.z2ProjectedCurrentReady /\
  g.plusMinusMatterCurrentsReady

theorem projected_current_requires_projected_dirac_action
    (g : ProjectedDiracMatterCurrentGate)
    (hReady : projectedDiracMatterCurrentReady g) :
    g.projectedDiracActionReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate
end JanusFormal

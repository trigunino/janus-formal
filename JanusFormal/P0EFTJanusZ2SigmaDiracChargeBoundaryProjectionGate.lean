import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaSpinorBundleProjectionGate
import JanusFormal.P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate

set_option autoImplicit false

structure DiracChargeBoundaryProjectionGate where
  curvedDiracChargeBibliographyChecked : Prop
  projectedDiracMatterCurrentGateDeclared : Prop
  spinorBundleProjectionGateDeclared : Prop
  spinorBoundaryProjectionMapGateDeclared : Prop
  plusChargeIntegralDeclared : Prop
  minusChargeIntegralDeclared : Prop
  z2SigmaChargeProjectionDeclared : Prop
  conservationAnomalyGuardDeclared : Prop
  boundaryLeakGuardDeclared : Prop
  observationalFitForbidden : Prop
  projectedDiracCurrentReady : Prop
  spinorProjectionReady : Prop
  plusChargeIntegralReady : Prop
  minusChargeIntegralReady : Prop
  z2SigmaProjectedChargeReady : Prop
  chargeBoundaryProjectionReady : Prop

def diracChargeBoundaryProjectionLedgerDeclared
    (g : DiracChargeBoundaryProjectionGate) : Prop :=
  g.curvedDiracChargeBibliographyChecked /\
  g.projectedDiracMatterCurrentGateDeclared /\
  g.spinorBundleProjectionGateDeclared /\
  g.spinorBoundaryProjectionMapGateDeclared /\
  g.plusChargeIntegralDeclared /\
  g.minusChargeIntegralDeclared /\
  g.z2SigmaChargeProjectionDeclared /\
  g.conservationAnomalyGuardDeclared /\
  g.boundaryLeakGuardDeclared /\
  g.observationalFitForbidden

def diracChargeBoundaryProjectionReady
    (g : DiracChargeBoundaryProjectionGate) : Prop :=
  diracChargeBoundaryProjectionLedgerDeclared g /\
  g.projectedDiracCurrentReady /\
  g.spinorProjectionReady /\
  g.plusChargeIntegralReady /\
  g.minusChargeIntegralReady /\
  g.z2SigmaProjectedChargeReady /\
  g.chargeBoundaryProjectionReady

theorem charge_projection_requires_projected_current
    (g : DiracChargeBoundaryProjectionGate)
    (hReady : diracChargeBoundaryProjectionReady g) :
    g.projectedDiracCurrentReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate
end JanusFormal

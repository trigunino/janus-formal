import JanusFormal.P0EFTJanusZ2SigmaFermionRouteSelectionGate
import JanusFormal.P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracNumberNormalizationGate

set_option autoImplicit false

structure DiracNumberNormalizationGate where
  noetherChargeBibliographyChecked : Prop
  diracChargeBoundaryProjectionGateDeclared : Prop
  diracCurrentChargeIntegralDeclared : Prop
  plusSectorChargeDeclared : Prop
  minusSectorChargeDeclared : Prop
  z2SigmaProjectionChargeDeclared : Prop
  anomalyOrBoundaryLeakGuardDeclared : Prop
  observationalFitForbidden : Prop
  diracChargeBoundaryProjectionReady : Prop
  plusChargeFixedByActionOrTopology : Prop
  minusChargeFixedByActionOrTopology : Prop
  projectedChargeFixedByZ2Sigma : Prop
  numberNormalizationsReady : Prop

def diracNumberNormalizationLedgerDeclared
    (g : DiracNumberNormalizationGate) : Prop :=
  g.noetherChargeBibliographyChecked /\
  g.diracChargeBoundaryProjectionGateDeclared /\
  g.diracCurrentChargeIntegralDeclared /\
  g.plusSectorChargeDeclared /\
  g.minusSectorChargeDeclared /\
  g.z2SigmaProjectionChargeDeclared /\
  g.anomalyOrBoundaryLeakGuardDeclared /\
  g.observationalFitForbidden

def diracNumberNormalizationReady
    (g : DiracNumberNormalizationGate) : Prop :=
  diracNumberNormalizationLedgerDeclared g /\
  g.diracChargeBoundaryProjectionReady /\
  g.plusChargeFixedByActionOrTopology /\
  g.minusChargeFixedByActionOrTopology /\
  g.projectedChargeFixedByZ2Sigma /\
  g.numberNormalizationsReady

theorem number_normalization_requires_plus_minus_charges
    (g : DiracNumberNormalizationGate)
    (hReady : diracNumberNormalizationReady g) :
    g.plusChargeFixedByActionOrTopology /\ g.minusChargeFixedByActionOrTopology := by
  exact And.intro hReady.2.2.1 hReady.2.2.2.1

theorem number_normalization_requires_boundary_projection
    (g : DiracNumberNormalizationGate)
    (hReady : diracNumberNormalizationReady g) :
    g.diracChargeBoundaryProjectionReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaDiracNumberNormalizationGate
end JanusFormal

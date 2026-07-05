import JanusFormal.P0EFTJanusZ2SigmaDiracNumberNormalizationGate
import JanusFormal.P0EFTJanusZ2SigmaProjectedBaryonNoetherChargeInputGate
import JanusFormal.P0EFTJanusZ2SigmaSpatialVolumeProjectiveSliceGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBaryonNumberDensityNoetherVolumeGate

set_option autoImplicit false

structure BaryonNumberDensityNoetherVolumeGate where
  projectedNoetherBaryonChargeDeclared : Prop
  activeSpatialVolumeDeclared : Prop
  z2CoverFactorAppliedExactlyOnce : Prop
  baryonNumberDensityFormulaDeclared : Prop
  observationalFitForbidden : Prop
  compressedPlanckLCDMRdForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  projectedBaryonChargeInputGatePassed : Prop
  spatialVolumeProjectiveSliceGatePassed : Prop
  projectedBaryonChargeFrontierDeclared : Prop
  spatialVolumeFrontierDeclared : Prop
  nearestBaryonDensityFrontierDeclared : Prop
  nearestBaryonDensityFrontierDiagnosticOnly : Prop
  projectedNoetherBaryonChargeDerived : Prop
  activeSpatialVolumeDerived : Prop
  baryonNumberDensityReady : Prop

def ledgerDeclared
    (g : BaryonNumberDensityNoetherVolumeGate) : Prop :=
  g.projectedNoetherBaryonChargeDeclared /\
  g.activeSpatialVolumeDeclared /\
  g.z2CoverFactorAppliedExactlyOnce /\
  g.baryonNumberDensityFormulaDeclared /\
  g.observationalFitForbidden /\
  g.compressedPlanckLCDMRdForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.projectedBaryonChargeFrontierDeclared /\
  g.spatialVolumeFrontierDeclared /\
  g.nearestBaryonDensityFrontierDeclared /\
  g.nearestBaryonDensityFrontierDiagnosticOnly

def gateReady
    (g : BaryonNumberDensityNoetherVolumeGate) : Prop :=
  ledgerDeclared g /\
  g.projectedBaryonChargeInputGatePassed /\
  g.spatialVolumeProjectiveSliceGatePassed /\
  g.projectedNoetherBaryonChargeDerived /\
  g.activeSpatialVolumeDerived /\
  g.baryonNumberDensityReady

theorem ready_requires_charge_and_volume
    (g : BaryonNumberDensityNoetherVolumeGate)
    (hReady : gateReady g) :
    g.projectedNoetherBaryonChargeDerived /\ g.activeSpatialVolumeDerived := by
  exact And.intro hReady.2.2.2.1 hReady.2.2.2.2.1

theorem ready_requires_upstream_gates
    (g : BaryonNumberDensityNoetherVolumeGate)
    (hReady : gateReady g) :
    g.projectedBaryonChargeInputGatePassed /\
    g.spatialVolumeProjectiveSliceGatePassed := by
  exact And.intro hReady.2.1 hReady.2.2.1

theorem diagnostic_density_frontier_does_not_supply_density
    (g : BaryonNumberDensityNoetherVolumeGate)
    (_hDiag : g.nearestBaryonDensityFrontierDiagnosticOnly)
    (hNoCharge : Not g.projectedNoetherBaryonChargeDerived) :
    Not (g.nearestBaryonDensityFrontierDiagnosticOnly /\ gateReady g) := by
  intro h
  exact hNoCharge h.2.2.2.2.1

end P0EFTJanusZ2SigmaBaryonNumberDensityNoetherVolumeGate
end JanusFormal

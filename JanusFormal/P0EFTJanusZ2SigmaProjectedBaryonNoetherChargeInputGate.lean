import JanusFormal.P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate
import JanusFormal.P0EFTJanusZ2SigmaDiracNumberNormalizationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectedBaryonNoetherChargeInputGate

set_option autoImplicit false

structure ProjectedBaryonNoetherChargeInputGate where
  projectedChargeFormulaDeclared : Prop
  projectedDiracCurrentReady : Prop
  chargeBoundaryProjectionReady : Prop
  freeProjectionWeightsForbidden : Prop
  observationalBaryonFitForbidden : Prop
  compressedPlanckLCDMRdForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  inputActiveDerivedManifestIsAuthoritative : Prop
  diracChargeBoundaryProjectionReady : Prop
  diracChargeBoundaryProjectionFrontierDeclared : Prop
  diracNumberNormalizationReady : Prop
  diracNumberNormalizationFrontierDeclared : Prop
  nearestProjectedBaryonChargeFrontierDeclared : Prop
  nearestProjectedBaryonChargeFrontierDiagnosticOnly : Prop
  projectedBaryonChargeManifestWritten : Prop
  gatePassed : Prop

def policyClosed
    (g : ProjectedBaryonNoetherChargeInputGate) : Prop :=
  g.projectedChargeFormulaDeclared /\
  g.freeProjectionWeightsForbidden /\
  g.observationalBaryonFitForbidden /\
  g.compressedPlanckLCDMRdForbidden /\
  g.archivedZ4ReuseForbidden

def gateReady
    (g : ProjectedBaryonNoetherChargeInputGate) : Prop :=
  policyClosed g /\
  (g.inputActiveDerivedManifestIsAuthoritative \/
    (g.diracChargeBoundaryProjectionReady /\ g.diracNumberNormalizationReady)) /\
  g.projectedDiracCurrentReady /\
  g.chargeBoundaryProjectionReady /\
  g.projectedBaryonChargeManifestWritten

theorem ready_requires_current_and_boundary_projection
    (g : ProjectedBaryonNoetherChargeInputGate)
    (hReady : gateReady g) :
    g.projectedDiracCurrentReady /\ g.chargeBoundaryProjectionReady := by
  exact And.intro hReady.2.2.1 hReady.2.2.2.1

theorem ready_requires_authoritative_manifest_or_upstream_dirac_closure
    (g : ProjectedBaryonNoetherChargeInputGate)
    (hReady : gateReady g) :
    g.inputActiveDerivedManifestIsAuthoritative \/
      (g.diracChargeBoundaryProjectionReady /\ g.diracNumberNormalizationReady) := by
  exact hReady.2.1

theorem nearest_projected_charge_frontier_diagnostic_does_not_write_charge
    (g : ProjectedBaryonNoetherChargeInputGate)
    (_hDiag : g.nearestProjectedBaryonChargeFrontierDiagnosticOnly)
    (hNoAuthority : Not g.inputActiveDerivedManifestIsAuthoritative)
    (hNoBoundary : Not g.diracChargeBoundaryProjectionReady) :
    Not (gateReady g) := by
  intro hReady
  cases hReady.2.1 with
  | inl hAuthority => exact hNoAuthority hAuthority
  | inr hUpstream => exact hNoBoundary hUpstream.1

end P0EFTJanusZ2SigmaProjectedBaryonNoetherChargeInputGate
end JanusFormal

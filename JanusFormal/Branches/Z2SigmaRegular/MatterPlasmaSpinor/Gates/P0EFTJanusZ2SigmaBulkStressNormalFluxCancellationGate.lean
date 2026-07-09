import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBulkStressOfAGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTangentNormalOrientationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate

set_option autoImplicit false

structure BulkStressNormalFluxCancellationGate where
  thinShellMomentumFluxBibliographyChecked : Prop
  bulkStressOfAGateDeclared : Prop
  tangentNormalOrientationGateDeclared : Prop
  plusFluxProjectionDeclared : Prop
  minusFluxProjectionDeclared : Prop
  z2FluxCancellationDeclared : Prop
  noFitTransparencyDecision : Prop
  observationalFitForbidden : Prop
  bulkStressPlusOfAReady : Prop
  bulkStressMinusOfAReady : Prop
  sigmaTangentsReady : Prop
  sigmaNormalsReady : Prop
  plusFluxProjectionReady : Prop
  minusFluxProjectionReady : Prop
  z2FluxCancellationDerived : Prop
  bulkStressNormalProjectionZeroDerived : Prop
  bulkStressOfAFrontierDeclared : Prop
  fluxProjectionDomainFrontierDeclared : Prop
  nearestBulkStressFluxFrontierDeclared : Prop
  nearestBulkStressFluxFrontierDiagnosticOnly : Prop

def bulkStressNormalFluxCancellationLedgerDeclared
    (g : BulkStressNormalFluxCancellationGate) : Prop :=
  g.thinShellMomentumFluxBibliographyChecked /\
  g.bulkStressOfAGateDeclared /\
  g.tangentNormalOrientationGateDeclared /\
  g.plusFluxProjectionDeclared /\
  g.minusFluxProjectionDeclared /\
  g.z2FluxCancellationDeclared /\
  g.noFitTransparencyDecision /\
  g.observationalFitForbidden

def bulkStressNormalFluxProjectionReady
    (g : BulkStressNormalFluxCancellationGate) : Prop :=
  bulkStressNormalFluxCancellationLedgerDeclared g /\
  g.bulkStressPlusOfAReady /\
  g.bulkStressMinusOfAReady /\
  g.sigmaTangentsReady /\
  g.sigmaNormalsReady /\
  g.plusFluxProjectionReady /\
  g.minusFluxProjectionReady /\
  g.bulkStressOfAFrontierDeclared /\
  g.fluxProjectionDomainFrontierDeclared /\
  g.nearestBulkStressFluxFrontierDeclared /\
  g.nearestBulkStressFluxFrontierDiagnosticOnly

def bulkStressNormalFluxCancellationReady
    (g : BulkStressNormalFluxCancellationGate) : Prop :=
  bulkStressNormalFluxProjectionReady g /\
  g.z2FluxCancellationDerived /\
  g.bulkStressNormalProjectionZeroDerived

theorem normal_flux_projection_requires_bulk_stress
    (g : BulkStressNormalFluxCancellationGate)
    (hReady : bulkStressNormalFluxProjectionReady g) :
    g.bulkStressPlusOfAReady /\ g.bulkStressMinusOfAReady := by
  exact ⟨hReady.2.1, hReady.2.2.1⟩

theorem normal_flux_projection_declares_frontiers
    (g : BulkStressNormalFluxCancellationGate)
    (hReady : bulkStressNormalFluxProjectionReady g) :
    g.bulkStressOfAFrontierDeclared /\
    g.fluxProjectionDomainFrontierDeclared /\
    g.nearestBulkStressFluxFrontierDeclared /\
    g.nearestBulkStressFluxFrontierDiagnosticOnly := by
  rcases hReady with ⟨_, _, _, _, _, _, _, hBulk, hDomain, hNearest, hDiag⟩
  exact ⟨hBulk, hDomain, hNearest, hDiag⟩

end P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate
end JanusFormal

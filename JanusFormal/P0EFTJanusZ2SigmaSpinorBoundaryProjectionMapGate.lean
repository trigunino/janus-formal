import JanusFormal.P0EFTJanusSigmaAPSPinLiftObligationGate
import JanusFormal.P0EFTJanusSigmaAPSParityAnomalyCancellationGate
import JanusFormal.P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
import JanusFormal.P0EFTJanusZ2SigmaTangentNormalOrientationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate

set_option autoImplicit false

structure SpinorBoundaryProjectionMapGate where
  apsProjectionBibliographyChecked : Prop
  localBoundaryProjectionBibliographyChecked : Prop
  boundarySpinorRestrictionGateDeclared : Prop
  apsPinLiftInputImported : Prop
  z2NormalOrientationInputImported : Prop
  projectionMapDeclared : Prop
  noFreeBoundaryPhase : Prop
  observationalFitForbidden : Prop
  sigmaBoundarySpinorDataReady : Prop
  sigmaApsBoundaryPinLiftClosed : Prop
  z2NormalOrientationReady : Prop
  projectionIdempotentReady : Prop
  projectionSelfAdjointReady : Prop
  z2SigmaSpinorProjectionReady : Prop

def spinorBoundaryProjectionMapLedgerDeclared
    (g : SpinorBoundaryProjectionMapGate) : Prop :=
  g.apsProjectionBibliographyChecked /\
  g.localBoundaryProjectionBibliographyChecked /\
  g.boundarySpinorRestrictionGateDeclared /\
  g.apsPinLiftInputImported /\
  g.z2NormalOrientationInputImported /\
  g.projectionMapDeclared /\
  g.noFreeBoundaryPhase /\
  g.observationalFitForbidden

def spinorBoundaryProjectionMapReady
    (g : SpinorBoundaryProjectionMapGate) : Prop :=
  spinorBoundaryProjectionMapLedgerDeclared g /\
  g.sigmaBoundarySpinorDataReady /\
  g.sigmaApsBoundaryPinLiftClosed /\
  g.z2NormalOrientationReady /\
  g.projectionIdempotentReady /\
  g.projectionSelfAdjointReady /\
  g.z2SigmaSpinorProjectionReady

theorem z2_sigma_spinor_projection_requires_aps_pin_lift
    (g : SpinorBoundaryProjectionMapGate)
    (hReady : spinorBoundaryProjectionMapReady g) :
    g.sigmaApsBoundaryPinLiftClosed := by
  exact hReady.2.2.1

theorem z2_sigma_spinor_projection_requires_no_free_phase
    (g : SpinorBoundaryProjectionMapGate)
    (hReady : spinorBoundaryProjectionMapReady g) :
    g.noFreeBoundaryPhase := by
  rcases hReady.1 with ⟨_, _, _, _, _, _, hNoFreePhase, _⟩
  exact hNoFreePhase

end P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate
end JanusFormal

import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusSigmaAPSPinLiftObligationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusSigmaAPSParityAnomalyCancellationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTangentNormalOrientationGate

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
  boundarySpinorRestrictionReady : Prop
  sigmaBoundarySpinorDataReady : Prop
  sigmaApsBoundaryPinLiftClosed : Prop
  z2CoorientationSignReady : Prop
  tangentNormalOrientationReady : Prop
  z2NormalOrientationReady : Prop
  unitNormalCliffordActionReady : Prop
  projectionIdempotentReady : Prop
  projectionSelfAdjointReady : Prop
  localZ2SigmaSpinorProjectionReady : Prop
  z2SigmaSpinorProjectionReady : Prop
  nearestSpinorProjectionFrontierDeclared : Prop
  nearestSpinorProjectionFrontierDiagnosticOnly : Prop

def spinorBoundaryProjectionMapLedgerDeclared
    (g : SpinorBoundaryProjectionMapGate) : Prop :=
  g.apsProjectionBibliographyChecked /\
  g.localBoundaryProjectionBibliographyChecked /\
  g.boundarySpinorRestrictionGateDeclared /\
  g.apsPinLiftInputImported /\
  g.z2NormalOrientationInputImported /\
  g.projectionMapDeclared /\
  g.noFreeBoundaryPhase /\
  g.observationalFitForbidden /\
  g.nearestSpinorProjectionFrontierDeclared /\
  g.nearestSpinorProjectionFrontierDiagnosticOnly

def spinorBoundaryProjectionMapReady
    (g : SpinorBoundaryProjectionMapGate) : Prop :=
  spinorBoundaryProjectionMapLedgerDeclared g /\
  g.boundarySpinorRestrictionReady /\
  g.sigmaBoundarySpinorDataReady /\
  g.sigmaApsBoundaryPinLiftClosed /\
  g.z2CoorientationSignReady /\
  g.tangentNormalOrientationReady /\
  g.z2NormalOrientationReady /\
  g.unitNormalCliffordActionReady /\
  g.projectionIdempotentReady /\
  g.projectionSelfAdjointReady /\
  g.z2SigmaSpinorProjectionReady

def localSpinorBoundaryProjectionMapReady
    (g : SpinorBoundaryProjectionMapGate) : Prop :=
  spinorBoundaryProjectionMapLedgerDeclared g /\
  g.sigmaApsBoundaryPinLiftClosed /\
  g.z2NormalOrientationReady /\
  g.unitNormalCliffordActionReady /\
  g.projectionIdempotentReady /\
  g.projectionSelfAdjointReady /\
  g.localZ2SigmaSpinorProjectionReady

theorem z2_sigma_spinor_projection_requires_aps_pin_lift
    (g : SpinorBoundaryProjectionMapGate)
    (hReady : spinorBoundaryProjectionMapReady g) :
    g.sigmaApsBoundaryPinLiftClosed := by
  rcases hReady with ⟨_, _, _, hAps, _, _, _, _, _, _, _⟩
  exact hAps

theorem z2_sigma_spinor_projection_requires_boundary_spinors
    (g : SpinorBoundaryProjectionMapGate)
    (hReady : spinorBoundaryProjectionMapReady g) :
    g.boundarySpinorRestrictionReady /\ g.sigmaBoundarySpinorDataReady := by
  rcases hReady with ⟨_, hBoundary, hSigma, _, _, _, _, _, _, _, _⟩
  exact And.intro hBoundary hSigma

theorem z2_sigma_spinor_projection_requires_normal_clifford_action
    (g : SpinorBoundaryProjectionMapGate)
    (hReady : spinorBoundaryProjectionMapReady g) :
    g.unitNormalCliffordActionReady := by
  rcases hReady with ⟨_, _, _, _, _, _, _, hClifford, _, _, _⟩
  exact hClifford

theorem z2_sigma_spinor_projection_requires_no_free_phase
    (g : SpinorBoundaryProjectionMapGate)
    (hReady : spinorBoundaryProjectionMapReady g) :
    g.noFreeBoundaryPhase := by
  rcases hReady.1 with ⟨_, _, _, _, _, _, hNoFreePhase, _, _, _⟩
  exact hNoFreePhase

theorem coorientation_sign_alone_does_not_close_spinor_projection
    (g : SpinorBoundaryProjectionMapGate)
    (hNoNormal : Not g.z2NormalOrientationReady) :
    Not (g.z2CoorientationSignReady /\ spinorBoundaryProjectionMapReady g) := by
  intro h
  rcases h.2 with ⟨_, _, _, _, _, _, hNormal, _, _, _, _⟩
  exact hNoNormal hNormal

theorem nearest_frontier_diagnostic_does_not_close_projection
    (g : SpinorBoundaryProjectionMapGate)
    (_hDiag : g.nearestSpinorProjectionFrontierDiagnosticOnly)
    (hNoClifford : Not g.unitNormalCliffordActionReady) :
    Not (g.nearestSpinorProjectionFrontierDiagnosticOnly /\
      spinorBoundaryProjectionMapReady g) := by
  intro h
  rcases h.2 with ⟨_, _, _, _, _, _, _, hClifford, _, _, _⟩
  exact hNoClifford hClifford

theorem local_projection_does_not_supply_boundary_spinor_data
    (g : SpinorBoundaryProjectionMapGate)
    (_hLocal : localSpinorBoundaryProjectionMapReady g)
    (hBoundary : g.boundarySpinorRestrictionReady /\ g.sigmaBoundarySpinorDataReady) :
    g.boundarySpinorRestrictionReady /\ g.sigmaBoundarySpinorDataReady := by
  exact hBoundary

end P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate
end JanusFormal

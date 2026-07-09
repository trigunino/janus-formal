import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4ShapeDiagnostic
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4OfficialPlanckGate
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4ScalarSourceScan
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4PhysicalClosureTriad

namespace JanusFormal
namespace P0EFTJanusZ4CMBDiagnosticMasterReport

set_option autoImplicit false

structure CMBDiagnosticMasterReport where
  publicShapeComparisonDone : Prop
  dominantPullsReported : Prop
  shapeOnlyGateDone : Prop
  officialPlanckAvailableGatesRerun : Prop
  compressedLCDMParametersNotUsed : Prop
  visibilitySilkLensingEnginePresent : Prop
  verdictDocumented : Prop
  officialPlanckGatePassed : Prop
  remainingLocksDocumented : Prop

def diagnosticInfrastructureComplete (r : CMBDiagnosticMasterReport) : Prop :=
  r.publicShapeComparisonDone /\
  r.dominantPullsReported /\
  r.shapeOnlyGateDone /\
  r.officialPlanckAvailableGatesRerun /\
  r.compressedLCDMParametersNotUsed /\
  r.visibilitySilkLensingEnginePresent /\
  r.verdictDocumented /\
  r.remainingLocksDocumented

def cmbObservationAccepted (r : CMBDiagnosticMasterReport) : Prop :=
  r.officialPlanckGatePassed

theorem diagnostic_complete_does_not_imply_observational_acceptance
    (r : CMBDiagnosticMasterReport)
    (_h : diagnosticInfrastructureComplete r)
    (hReject : Not r.officialPlanckGatePassed) :
    Not (cmbObservationAccepted r) := by
  intro h
  exact hReject h

theorem diagnostic_complete_includes_verdict_and_locks
    (r : CMBDiagnosticMasterReport)
    (h : diagnosticInfrastructureComplete r) :
    r.verdictDocumented /\ r.remainingLocksDocumented := by
  exact And.intro h.right.right.right.right.right.right.left h.right.right.right.right.right.right.right

end P0EFTJanusZ4CMBDiagnosticMasterReport
end JanusFormal

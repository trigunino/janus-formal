import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ControlledGeometricSolverBranch

namespace JanusFormal
namespace P0EFTJanusNegativeSectorCMBImprint

set_option autoImplicit false

structure NegativeSectorCMBImprint where
  localPDFRegistered : Prop
  negativeSectorImprintHypothesisDeclared : Prop
  fixedScaleRatioDeclared : Prop
  fixedCRatioDeclared : Prop
  noContinuousFitFactorUsed : Prop
  imprintCandidatesMeasured : Prop
  ttPeakMeasured : Prop
  polarizationGuardMeasured : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def imprintDiagnosticReady (i : NegativeSectorCMBImprint) : Prop :=
  i.localPDFRegistered /\
  i.negativeSectorImprintHypothesisDeclared /\
  i.fixedScaleRatioDeclared /\
  i.fixedCRatioDeclared /\
  i.noContinuousFitFactorUsed /\
  i.imprintCandidatesMeasured /\
  i.ttPeakMeasured /\
  i.polarizationGuardMeasured

def promotableImprintReady (i : NegativeSectorCMBImprint) : Prop :=
  imprintDiagnosticReady i /\
  i.ttPeakMeasured /\
  i.polarizationGuardMeasured

theorem imprint_uses_no_fit_factor
    (i : NegativeSectorCMBImprint)
    (h : imprintDiagnosticReady i) :
    i.noContinuousFitFactorUsed := by
  exact h.right.right.right.right.left

theorem imprint_keeps_solver_frozen
    (i : NegativeSectorCMBImprint)
    (_h : imprintDiagnosticReady i)
    (hFrozen : Not i.solverNumericsModified) :
    Not i.solverNumericsModified := by
  exact hFrozen

theorem imprint_does_not_claim_planck
    (i : NegativeSectorCMBImprint)
    (_h : imprintDiagnosticReady i)
    (hNoClaim : Not i.planckValidationClaimed) :
    Not i.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusNegativeSectorCMBImprint
end JanusFormal

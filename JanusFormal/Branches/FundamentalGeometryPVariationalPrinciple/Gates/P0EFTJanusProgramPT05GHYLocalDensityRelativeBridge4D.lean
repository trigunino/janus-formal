import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

/-!
# T05 GHY local-density relative bridge

This module places the existing completed Candidate-A GHY boundary integrand
in a typed non-null local-density cochain.  Its first-sheet evaluation is the
existing continuous integral and is definitionally the completed GHY action.
The density integral is embedded in the non-null slot of Gate 819.

No existing theorem identifies this mobile GHY integral alone with the bulk
or joint incidence of Gate 819, so no such identity is asserted here.  The
full local jet first-variation bicomplex remains open.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The completed GHY integrand as a genuine typed density on the non-null
orientation boundary. -/
structure ProgramPT05GHYLocalDensityCochain
    (period : Real) (hPeriod : period ≠ 0) where
  nonNullBoundaryDensity : CandidateANormalBoundaryScalarField period hPeriod

/-- The already constructed Candidate-A GHY integrand. -/
def programPT05CanonicalGHYLocalDensityCochain
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current :
      CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    ProgramPT05GHYLocalDensityCochain period hPeriod where
  nonNullBoundaryDensity :=
    candidateANormalBoundaryGHYIntegrandFiberEvaluation
      period hPeriod einsteinScale metric current

/-- Continuous first-sheet integration of the typed GHY density. -/
def programPT05GHYFirstSheetDensityIntegral
    (density : ProgramPT05GHYLocalDensityCochain period hPeriod) : Real :=
  candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
    density.nonNullBoundaryDensity

/-- Evaluation of the canonical density is exactly the existing completed GHY
action, without a new action postulate. -/
theorem programPT05CanonicalGHYFirstSheetDensityIntegral_eq_action
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current :
      CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    programPT05GHYFirstSheetDensityIntegral period hPeriod
        (programPT05CanonicalGHYLocalDensityCochain period hPeriod
          einsteinScale metric current) =
      candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric current := by
  rfl

/-- The same evaluation written as the actual integral over the canonical
first-sheet parametrization. -/
theorem programPT05CanonicalGHYFirstSheetDensityIntegral_eq_integral
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current :
      CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    programPT05GHYFirstSheetDensityIntegral period hPeriod
        (programPT05CanonicalGHYLocalDensityCochain period hPeriod
          einsteinScale metric current) =
      ∫ base,
        candidateANormalBoundaryGHYIntegrandFiberEvaluation
            period hPeriod einsteinScale metric current
          (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
        ∂canonicalLatitudeBaseMeasure period := by
  rw [programPT05CanonicalGHYFirstSheetDensityIntegral_eq_action]
  exact
    candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation_eq_integral
      period hPeriod einsteinScale metric current

/-- Support extension of the integrated GHY density to the non-null boundary
slot in horizontal degree three of Gate 819. -/
def programPT05GHYDensityIntegratedRelativeCochain
    (density : ProgramPT05GHYLocalDensityCochain period hPeriod) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0
  | .bulk => 0
  | .nonNullBoundary =>
      (programPT05GHYFirstSheetDensityIntegral period hPeriod density, 0)
  | .nullBoundary => 0
  | .joint => 0

@[simp]
theorem programPT05GHYDensityIntegratedRelativeCochain_nonNullBoundary
    (density : ProgramPT05GHYLocalDensityCochain period hPeriod) :
    programPT05GHYDensityIntegratedRelativeCochain period hPeriod density
        .nonNullBoundary =
      (programPT05GHYFirstSheetDensityIntegral period hPeriod density, 0) := by
  rfl

/-- The canonical non-null coefficient in Gate 819 is the completed GHY
action. -/
theorem programPT05CanonicalGHYIntegratedRelativeCochain_nonNull_eq_action
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current :
      CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    programPT05GHYDensityIntegratedRelativeCochain period hPeriod
        (programPT05CanonicalGHYLocalDensityCochain period hPeriod
          einsteinScale metric current) .nonNullBoundary =
      (candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric current, 0) := by
  rw [programPT05GHYDensityIntegratedRelativeCochain_nonNullBoundary,
    programPT05CanonicalGHYFirstSheetDensityIntegral_eq_action]

end
end P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
end JanusFormal

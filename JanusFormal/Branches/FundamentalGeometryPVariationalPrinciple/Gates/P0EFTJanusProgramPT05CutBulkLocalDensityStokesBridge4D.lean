import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentCanonicalStokes4D

/-!
# T05 cut-bulk local-density Stokes bridge

This module puts an already proved local four-dimensional bulk-current density
and its actual cut-boundary density into the relative incidence pattern of Gate
819.  Their integrations obey the existing global cut-bulk Stokes theorem, so
the non-null component of the Gate-819 horizontal differential is geometric.

This is one scalar-current sector.  It does not supply the T03 metric/GHY,
null-boundary, joint, or LL jet Lagrangian densities; those sectors remain open.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Interval
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentCanonicalStokes4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A genuinely local density cochain on the realized cut-bulk/non-null pair. -/
structure ProgramPT05CutBulkNonNullLocalDensityCochain
    (period : Real) (hPeriod : period ≠ 0) where
  bulkDensity : CanonicalLatitudeBase → Real → Real
  nonNullBoundaryDensity : CanonicalLatitudeBase → Real

/-- The two strata for which this scalar-current construction supplies no local
density.  They are recorded explicitly rather than filled by zero densities. -/
inductive ProgramPT05CutBulkOpenLocalDensitySector
  | nullBoundary
  | joint
  deriving DecidableEq

/-- Existing geometric bulk current and first-sheet boundary current, viewed as
a local density cochain on the realized two-stratum sector. -/
def programPT05CanonicalCutBulkLocalDensityCochain
    (field test : SmoothQuotientField period hPeriod Real) :
    ProgramPT05CutBulkNonNullLocalDensityCochain period hPeriod where
  bulkDensity base normal :=
    deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
      (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal
  nonNullBoundaryDensity base :=
    cutBoundaryScalarCurrent period hPeriod field test
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)

/-- Product-collar integration of the local bulk density. -/
def programPT05CutBulkDensityIntegral
    (density : ProgramPT05CutBulkNonNullLocalDensityCochain period hPeriod) : Real :=
  ∫ base, (∫ normal in (0 : Real)..1, density.bulkDensity base normal)
    ∂(canonicalLatitudeBaseMeasure period)

/-- Integration of the local non-null boundary density. -/
def programPT05NonNullBoundaryDensityIntegral
    (density : ProgramPT05CutBulkNonNullLocalDensityCochain period hPeriod) : Real :=
  ∫ base, density.nonNullBoundaryDensity base
    ∂(canonicalLatitudeBaseMeasure period)

/-- The existing global Stokes law evaluates the local density cochain. -/
theorem programPT05CanonicalCutBulkLocalDensity_stokes
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    programPT05CutBulkDensityIntegral period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod field test) =
      -programPT05NonNullBoundaryDensityIntegral period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod field test) := by
  simpa [programPT05CutBulkDensityIntegral,
    programPT05NonNullBoundaryDensityIntegral,
    programPT05CanonicalCutBulkLocalDensityCochain] using
      productCanonicalCollarIntegral_deriv_globalCurrent_eq_neg_boundary
        period hPeriod massSquared field test

/-- Put the integrated bulk density into Gate 819's physical cochain. -/
def programPT05CutBulkDensityIntegratedCochain
    (density : ProgramPT05CutBulkNonNullLocalDensityCochain period hPeriod) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk => (programPT05CutBulkDensityIntegral period hPeriod density, 0)
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => 0

/-- Put the integrated geometric boundary value in the realized non-null slot. -/
def programPT05NonNullBoundaryDensityIntegratedCochain
    (density : ProgramPT05CutBulkNonNullLocalDensityCochain period hPeriod) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 5 0
  | .bulk => 0
  | .nonNullBoundary =>
      (-programPT05NonNullBoundaryDensityIntegral period hPeriod density, 0)
  | .nullBoundary => 0
  | .joint => 0

/-- On the realized non-null face, the genuine Stokes law is exactly Gate 819's
oriented `bulk → nonNullBoundary` incidence. -/
theorem programPT05CanonicalCutBulkLocalDensity_dH_nonNull
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    (programPT05ExactT03RelativeBicomplex.dH 4 0
      (programPT05CutBulkDensityIntegratedCochain period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain
          period hPeriod field test))) .nonNullBoundary =
    (programPT05NonNullBoundaryDensityIntegratedCochain period hPeriod
      (programPT05CanonicalCutBulkLocalDensityCochain
        period hPeriod field test)) .nonNullBoundary := by
  change
    (programPT05CutBulkDensityIntegral period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain
          period hPeriod field test), 0) =
      (-programPT05NonNullBoundaryDensityIntegral period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain
          period hPeriod field test), 0)
  rw [programPT05CanonicalCutBulkLocalDensity_stokes
    period hPeriod massSquared field test]

end
end P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
end JanusFormal

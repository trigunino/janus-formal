import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalScalarGreenBoundaryDomain4D

/-!
# Dirichlet closure of the oriented scalar Green--Stokes obstruction

The two oriented cut sheets do not cancel for arbitrary smooth scalar fields.
Program P therefore fixes the homogeneous Dirichlet line as its first physical
boundary domain.  On that domain the exact oriented boundary form vanishes,
the measured cut-bulk Stokes identity closes, and the latitude Euler sector
satisfies the complete metric Green--Stokes identity.

No universal oriented-flux cancellation is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarDirichletOrientedGreenStokesClosure4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D
open P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarGreenBoundaryDomain4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The preferred smooth physical boundary domain for the first complete
oriented Green--Stokes realization. -/
def canonicalPhysicalScalarPreferredGreenBoundaryCondition :
    CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod :=
  dirichletScalarGreenBoundaryCondition period hPeriod

/-- Homogeneous Dirichlet data kill the genuinely oriented two-sheet flux.
This is the missing boundary input in the obstruction equivalence. -/
theorem canonicalPhysicalScalarDirichlet_orientedBoundary_zero
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod field)
    (hTest : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod test) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test = 0 := by
  change cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0
  exact cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_dirichlet
    period hPeriod field test hField hTest

/-- Exact measured Green--Stokes identity on the selected Dirichlet domain. -/
theorem canonicalPhysicalScalarDirichlet_measuredGreenStokes
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ =
      -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test :=
  cutBulkGlobalMeasuredGreenStokes
    period hPeriod massSquared field test

/-- The exact measured cut-bulk divergence vanishes on the Dirichlet domain;
no Euler equation is needed. -/
theorem canonicalPhysicalScalarDirichlet_cutBulkDivergence_zero
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod field)
    (hTest : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod test) :
    cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
        field test Set.univ = 0 :=
  cutBulkCanonicalDivergenceMeasure_univ_eq_zero_of_greenBoundaryCondition
    period hPeriod massSquared
      (canonicalPhysicalScalarPreferredGreenBoundaryCondition period hPeriod)
      field test hField hTest

/-- The complete metric Green--Stokes formula holds on the Dirichlet Euler
domain, with the genuine oriented boundary functional. -/
theorem canonicalPhysicalScalarDirichlet_metricGreenStokes
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod field)
    (hTest : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test :=
  cutBulkGlobalMetricGreenStokes_of_greenBoundaryCondition
    period hPeriod massSquared
      (canonicalPhysicalScalarPreferredGreenBoundaryCondition period hPeriod)
      field test hFieldEuler hTestEuler hField hTest

/-- The metric skew pairing consequently vanishes on the same domain. -/
theorem canonicalPhysicalScalarDirichlet_metricDivergence_zero
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod field)
    (hTest : CanonicalLatitudeScalarDirichletBoundaryCondition
      period hPeriod test) :
    canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
      massSquared field test = 0 :=
  canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_zero_of_greenBoundaryCondition
    period hPeriod massSquared
      (canonicalPhysicalScalarPreferredGreenBoundaryCondition period hPeriod)
      field test hFieldEuler hTestEuler hField hTest

/-- Unconditional closure certificate for the selected Program P boundary
sector.  The universal wave naturality and every remaining oriented
Green--Stokes conclusion are theorem-generated. -/
theorem canonicalPhysicalScalarDirichletOrientedGreenStokesClosure_certificate
    (massSquared : Real) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod ∧
      (∀ field test : SmoothQuotientField period hPeriod Real,
        CanonicalLatitudeScalarDirichletBoundaryCondition
            period hPeriod field →
          CanonicalLatitudeScalarDirichletBoundaryCondition
            period hPeriod test →
          cutBulkGlobalOrientedScalarCurrentIntegral
              period hPeriod field test = 0 ∧
            2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
                  field test Set.univ =
                -cutBulkGlobalOrientedScalarCurrentIntegral
                  period hPeriod field test ∧
              cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
                field test Set.univ = 0) ∧
      ∀ field test : SmoothQuotientField period hPeriod Real,
        CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field →
          CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test →
          CanonicalLatitudeScalarDirichletBoundaryCondition
            period hPeriod field →
          CanonicalLatitudeScalarDirichletBoundaryCondition
            period hPeriod test →
          2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
                period hPeriod massSquared field test =
              -cutBulkGlobalOrientedScalarCurrentIntegral
                period hPeriod field test ∧
            canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
              period hPeriod massSquared field test = 0 := by
  refine ⟨(CanonicalPhysicalScalarIntrinsicWaveData.canonical period hPeriod)
      |>.toWaveAtlasNaturality period hPeriod, ?_, ?_⟩
  · intro field test hField hTest
    exact ⟨canonicalPhysicalScalarDirichlet_orientedBoundary_zero
        period hPeriod field test hField hTest,
      canonicalPhysicalScalarDirichlet_measuredGreenStokes
        period hPeriod massSquared field test,
      canonicalPhysicalScalarDirichlet_cutBulkDivergence_zero
        period hPeriod massSquared field test hField hTest⟩
  · intro field test hFieldEuler hTestEuler hField hTest
    exact ⟨canonicalPhysicalScalarDirichlet_metricGreenStokes
        period hPeriod massSquared field test hFieldEuler hTestEuler
          hField hTest,
      canonicalPhysicalScalarDirichlet_metricDivergence_zero
        period hPeriod massSquared field test hFieldEuler hTestEuler
          hField hTest⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarDirichletOrientedGreenStokesClosure4D
end JanusFormal

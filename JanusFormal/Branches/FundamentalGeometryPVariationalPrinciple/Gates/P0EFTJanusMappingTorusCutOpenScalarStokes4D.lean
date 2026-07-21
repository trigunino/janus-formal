import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjectionEuler4D

/-!
# Concrete Green--Stokes interface on the cut-open bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutOpenScalarStokes4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceMeasuredStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceOrientedBoundaryObstruction4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjection4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjectionEuler4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- General measured Green--Stokes formula on the concrete cut-open bulk. -/
theorem cutOpenScalarMeasuredGreenStokes
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    2 * cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure period hPeriod
        massSquared field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) :=
  two_mul_cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure_univ_eq_neg_flux
    period hPeriod massSquared field test hField hTest

/-- For arbitrary Euler data, the metric-volume formula is equivalent to
vanishing of the genuinely oriented two-sheet period. -/
theorem cutOpenScalarMetricGreenStokes_iff_orientedPeriod_zero
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    (2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
        -twoSheetOrientedScalarCurrentIntegral period hPeriod field test) ↔
      twoSheetOrientedScalarCurrentIntegral period hPeriod field test = 0 :=
  completeMetricStokes_iff_twoSheetOrientedFlux_zero_of_euler
    period hPeriod massSquared field test hField hTest

/-- The concrete metric formula is unconditional in the PT-fixed Euler
sector. -/
theorem cutOpenScalarMetricGreenStokes_of_ptFixed
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (hFieldPT : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTestPT : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod field test :=
  completeMetricStokes_of_euler_of_ptFixed period hPeriod massSquared
    field test hFieldEuler hTestEuler hFieldPT hTestPT

/-- Every pair of Euler solutions has a canonical PT-even projection for
which the concrete metric Green--Stokes formula holds. -/
theorem cutOpenScalarMetricGreenStokes_of_ptEvenProjection
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) :=
  projectedCompleteMetricStokes period hPeriod massSquared field test hField hTest

/-- Homogeneous Dirichlet Euler data provide the second concrete closed
sector without using PT projection. -/
theorem cutOpenScalarMetricGreenStokes_of_dirichletEuler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) :=
  two_mul_canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_neg_flux_of_dirichletEuler
    period hPeriod massSquared field test hField hTest

end
end P0EFTJanusMappingTorusCutOpenScalarStokes4D
end JanusFormal

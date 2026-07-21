import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceFullEulerBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D

/-!
# Oriented boundary obstruction for the complete metric Stokes formula
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceOrientedBoundaryObstruction4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Under the latitude Euler equations, the exact tangential cancellation is
equivalent to vanishing of the genuinely oriented two-sheet boundary flux. -/
theorem canonicalLatitudeCenteredMetricTangentialCancellation_iff_twoSheetOrientedFlux_zero_of_euler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    CanonicalLatitudeCenteredMetricTangentialCancellation period hPeriod
        massSquared field test ↔
      twoSheetOrientedScalarCurrentIntegral period hPeriod field test = 0 := by
  rw [canonicalLatitudeCenteredMetricTangentialCancellation_iff_measuredGreenCurrent_zero_of_euler
      period hPeriod massSquared field test hField hTest,
    twoSheetOrientedScalarCurrentIntegral_eq_two_mul_genuineFlux,
    canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test 0 (by norm_num)]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    nlinarith

/-- The desired complete metric-volume Stokes identity itself is equivalent
to vanishing of the oriented boundary flux.  The already proved unoriented
deck cancellation cannot be substituted for this statement. -/
theorem completeMetricStokes_iff_twoSheetOrientedFlux_zero_of_euler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    (2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
        -twoSheetOrientedScalarCurrentIntegral period hPeriod field test) ↔
      twoSheetOrientedScalarCurrentIntegral period hPeriod field test = 0 := by
  have hStokesCancellation :
      (2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
            massSquared field test =
          -twoSheetOrientedScalarCurrentIntegral period hPeriod field test) ↔
        CanonicalLatitudeCenteredMetricTangentialCancellation period hPeriod
          massSquared field test := by
    unfold CanonicalLatitudeCenteredMetricTangentialCancellation
    rw [productHalfCollarIntegral_metricDensitizedDivergence_eq_neg_throatFlux,
      twoSheetOrientedScalarCurrentIntegral_eq_two_mul_genuineFlux,
      canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
        period hPeriod field test 0 (by norm_num)]
    constructor <;> intro h <;> linarith
  exact hStokesCancellation.trans
    (canonicalLatitudeCenteredMetricTangentialCancellation_iff_twoSheetOrientedFlux_zero_of_euler
      period hPeriod massSquared field test hField hTest)

end
end P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceOrientedBoundaryObstruction4D
end JanusFormal

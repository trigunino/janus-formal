import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeEulerWronskianNoGo4D

/-!
# Global odd-symmetry criterion for the oriented Green flux
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeOrientedFluxOddSymmetry4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceOrientedBoundaryObstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Non-circular global datum sufficient to kill the first-sheet period: a
measure-preserving base symmetry under which the pointwise current is odd. -/
structure CanonicalLatitudeGreenCurrentOddSymmetry
    (field test : SmoothQuotientField period hPeriod Real) where
  symmetry : CanonicalLatitudeBase ≃ᵐ CanonicalLatitudeBase
  measurePreserving : MeasurePreserving symmetry
    (canonicalLatitudeBaseMeasure period) (canonicalLatitudeBaseMeasure period)
  current_odd : ∀ base,
    canonicalLatitudeScalarGreenCurrent period hPeriod field test
        (symmetry base) 0 =
      -canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0

theorem measuredGreenCurrent_zero_of_oddSymmetry
    (field test : SmoothQuotientField period hPeriod Real)
    (symmetry : CanonicalLatitudeGreenCurrentOddSymmetry period hPeriod field test) :
    canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 = 0 := by
  unfold canonicalLatitudeMeasuredScalarGreenCurrent
  have hInvariant := symmetry.measurePreserving.integral_comp
    symmetry.symmetry.measurableEmbedding
    (fun base => canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0)
  have hNeg :
      (∫ base, canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0
          ∂canonicalLatitudeBaseMeasure period) =
        -(∫ base, canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0
          ∂canonicalLatitudeBaseMeasure period) := by
    calc
      _ = ∫ base, canonicalLatitudeScalarGreenCurrent period hPeriod field test
          (symmetry.symmetry base) 0 ∂canonicalLatitudeBaseMeasure period := hInvariant.symm
      _ = ∫ base, -canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0
          ∂canonicalLatitudeBaseMeasure period := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall symmetry.current_odd
      _ = -_ := integral_neg _
  linarith

theorem twoSheetOrientedFlux_zero_of_oddSymmetry
    (field test : SmoothQuotientField period hPeriod Real)
    (symmetry : CanonicalLatitudeGreenCurrentOddSymmetry period hPeriod field test) :
    twoSheetOrientedScalarCurrentIntegral period hPeriod field test = 0 := by
  rw [twoSheetOrientedScalarCurrentIntegral_eq_two_mul_genuineFlux,
    canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test 0 (by norm_num),
    measuredGreenCurrent_zero_of_oddSymmetry period hPeriod field test symmetry,
    mul_zero]

theorem completeMetricStokes_of_euler_of_oddSymmetry
    (massSquared : Real) (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (symmetry : CanonicalLatitudeGreenCurrentOddSymmetry period hPeriod field test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  apply (completeMetricStokes_iff_twoSheetOrientedFlux_zero_of_euler
    period hPeriod massSquared field test hField hTest).2
  exact twoSheetOrientedFlux_zero_of_oddSymmetry period hPeriod field test symmetry

end
end P0EFTJanusMappingTorusCanonicalLatitudeOrientedFluxOddSymmetry4D
end JanusFormal

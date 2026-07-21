import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

/-!
# Measured Stokes formula for the genuine cut-bulk Green-current flux
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Interval
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentHalfCollarStokes4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Measured normal flux of the genuine intrinsic Green current. -/
def canonicalMeasuredCutBulkIntrinsicGreenNormalFlux
    (field test : SmoothQuotientField period hPeriod Real)
    (normal : Real) : Real :=
  ∫ base, canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod
    field test base normal ∂canonicalLatitudeBaseMeasure period

theorem canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (normal : Real) (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test normal =
      canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod
        field test normal := by
  unfold canonicalMeasuredCutBulkIntrinsicGreenNormalFlux
    canonicalLatitudeMeasuredScalarGreenCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test base normal hNormal

/-- Positive-half-collar Stokes, now stated directly with the genuine
intrinsic vector-current normal flux. -/
theorem productHalfCollarIntegral_cutoffDivergence_eq_neg_genuineFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ base, (∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal) ∂canonicalLatitudeBaseMeasure period =
      -canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0 := by
  rw [productHalfCollarIntegral_cutoffCurrentDivergence_eq_neg_throatFlux,
    canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test 0 (by norm_num)]

/-- The oriented two-sheet boundary current is twice the measured genuine
normal flux on the first throat sheet. -/
theorem twoSheetOrientedScalarCurrentIntegral_eq_two_mul_genuineFlux
    (field test : SmoothQuotientField period hPeriod Real) :
    twoSheetOrientedScalarCurrentIntegral period hPeriod field test =
      2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0 := by
  rw [twoSheetOrientedScalarCurrentIntegral_eq_two_mul_first,
    firstSheetOrientedScalarCurrentIntegral_eq_current,
    ← measuredScalarGreenCurrent_zero_eq_firstSheetIntegral,
    ← canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test 0 (by norm_num)]

/-- Existing cut-bulk divergence measure with boundary term realized by the
genuine intrinsic Green-current flux. -/
theorem two_mul_cutBulkCanonicalDivergenceMeasure_univ_eq_neg_genuineFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
        field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [two_mul_cutBulkCanonicalDivergenceMeasure_univ_eq_neg_boundary,
    twoSheetOrientedScalarCurrentIntegral_eq_two_mul_genuineFlux]

end
end P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D

/-!
# Canonical Stokes identity for the global cut-bulk current

The integrated normal derivative of the actual global bulk current along its
canonical positive collar equals the negative first-sheet boundary current.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkScalarCurrentCanonicalStokes4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Interval
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem intervalIntegral_deriv_globalCurrent_eq_divergence
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    ∫ normal in (0 : Real)..1,
        deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal =
      ∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal := by
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le zero_le_one]
  filter_upwards [(volume : Measure Real).ae_ne (1 : Real)] with normal hNe hNormal
  exact deriv_cutBulkScalarCurrent_canonicalCollarPath period hPeriod
    massSquared field test base normal
      ⟨hNormal.1, lt_of_le_of_ne hNormal.2 hNe⟩

/-- Stokes/FTC identity written directly with the global bulk current and the
actual first-sheet boundary current. -/
theorem productCanonicalCollarIntegral_deriv_globalCurrent_eq_neg_boundary
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ base, (∫ normal in (0 : Real)..1,
        deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal)
        ∂canonicalLatitudeBaseMeasure period =
      -∫ base, cutBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
        ∂canonicalLatitudeBaseMeasure period := by
  simp_rw [intervalIntegral_deriv_globalCurrent_eq_divergence
    period hPeriod massSquared field test]
  exact productHalfCollarIntegral_eq_neg_firstSheetBoundaryCurrent
    period hPeriod massSquared field test

/-- Two-sheet oriented form, with the exact doubling forced by the connected
orientation-double boundary. -/
theorem two_mul_productCanonicalCollarIntegral_deriv_globalCurrent_eq_neg_boundary
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * (∫ base, (∫ normal in (0 : Real)..1,
        deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal)
        ∂canonicalLatitudeBaseMeasure period) =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  rw [productCanonicalCollarIntegral_deriv_globalCurrent_eq_neg_boundary
      period hPeriod massSquared field test,
    twoSheetOrientedScalarCurrentIntegral_eq_two_mul_first,
    firstSheetOrientedScalarCurrentIntegral_eq_current]
  ring

end
end P0EFTJanusMappingTorusCutBulkScalarCurrentCanonicalStokes4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D

/-!
# Oriented Green current on the exact global cut-bulk boundary

The cut-open bulk already carries a genuine manifold boundary, canonically
homeomorphic to the orientation-double throat.  This file transports the two
canonical boundary sheets through that homeomorphism and defines the oriented
boundary functional directly on the exact boundary subtype.

The positive boundary measure still gives the expected unoriented cancellation.
The oriented functional instead inserts the outward-normal signs before
integration and therefore agrees with the previously constructed two-sheet
Green-current period.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCutBoundaryOrientedFluxSign4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBoundaryGlobalHomeomorph4D
open P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The first canonical latitude sheet, now regarded as a point of the exact
manifold boundary of the global cut bulk. -/
def canonicalLatitudeCutBulkGlobalBoundaryFirstLift
    (base : CanonicalLatitudeBase) :
    CutBulkGlobalBoundary period hPeriod := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact cutBoundaryGlobalBoundaryHomeomorph period hPeriod
    (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)

/-- The deck-related second latitude sheet on the exact global boundary. -/
def canonicalLatitudeCutBulkGlobalBoundarySecondLift
    (base : CanonicalLatitudeBase) :
    CutBulkGlobalBoundary period hPeriod := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact cutBoundaryGlobalBoundaryHomeomorph period hPeriod
    (canonicalLatitudeCutBoundarySecondLift period hPeriod base)

@[simp] theorem cutBulkGlobalBoundaryScalarCurrent_firstLift
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base) =
      cutBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  simp [cutBulkGlobalBoundaryScalarCurrent,
    canonicalLatitudeCutBulkGlobalBoundaryFirstLift]

@[simp] theorem cutBulkGlobalBoundaryScalarCurrent_secondLift
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkGlobalBoundarySecondLift period hPeriod base) =
      cutBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBoundarySecondLift period hPeriod base) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  simp [cutBulkGlobalBoundaryScalarCurrent,
    canonicalLatitudeCutBulkGlobalBoundarySecondLift]

/-- Canonical oriented boundary functional on the exact global boundary.

The first and second terms use the two canonical latitude sheets and insert the
corresponding outward-normal signs before integration.  This is deliberately
different from integration against the positive unoriented boundary measure. -/
def cutBulkGlobalOrientedBoundaryIntegral
    (function : CutBulkGlobalBoundary period hPeriod → Real) : Real :=
  (∫ base, orientedCutLiftFlux .increasing
      (function
        (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base))
      ∂canonicalLatitudeBaseMeasure period) +
    ∫ base, orientedCutLiftFlux .decreasing
      (function
        (canonicalLatitudeCutBulkGlobalBoundarySecondLift period hPeriod base))
      ∂canonicalLatitudeBaseMeasure period

/-- The descended scalar Green current evaluated by the exact global oriented
boundary functional. -/
def cutBulkGlobalOrientedScalarCurrentIntegral
    (field test : SmoothQuotientField period hPeriod Real) : Real :=
  cutBulkGlobalOrientedBoundaryIntegral period hPeriod
    (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test)

/-- Transport through the exact boundary homeomorphism does not change the
first oriented sheet contribution. -/
theorem cutBulkGlobalFirstSheetOrientedCurrentIntegral_eq
    (field test : SmoothQuotientField period hPeriod Real) :
    (∫ base, orientedCutLiftFlux .increasing
        (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base))
        ∂canonicalLatitudeBaseMeasure period) =
      firstSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  unfold firstSheetOrientedScalarCurrentIntegral firstSheetOrientedScalarCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base => by
    rw [cutBulkGlobalBoundaryScalarCurrent_firstLift]

/-- Transport through the exact boundary homeomorphism does not change the
second oriented sheet contribution. -/
theorem cutBulkGlobalSecondSheetOrientedCurrentIntegral_eq
    (field test : SmoothQuotientField period hPeriod Real) :
    (∫ base, orientedCutLiftFlux .decreasing
        (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkGlobalBoundarySecondLift period hPeriod base))
        ∂canonicalLatitudeBaseMeasure period) =
      secondSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  unfold secondSheetOrientedScalarCurrentIntegral secondSheetOrientedScalarCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base => by
    rw [cutBulkGlobalBoundaryScalarCurrent_secondLift]

/-- The boundary functional on the exact manifold boundary is exactly the
previous two-sheet oriented period. -/
theorem cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
      twoSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  unfold cutBulkGlobalOrientedScalarCurrentIntegral
    cutBulkGlobalOrientedBoundaryIntegral
    twoSheetOrientedScalarCurrentIntegral
  rw [cutBulkGlobalFirstSheetOrientedCurrentIntegral_eq,
    cutBulkGlobalSecondSheetOrientedCurrentIntegral_eq]

/-- Both oriented boundary sheets give the same contribution after the current
and outward-normal signs are combined. -/
theorem cutBulkGlobalSecondSheetOrientedCurrentIntegral_eq_first
    (field test : SmoothQuotientField period hPeriod Real) :
    (∫ base, orientedCutLiftFlux .decreasing
        (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkGlobalBoundarySecondLift period hPeriod base))
        ∂canonicalLatitudeBaseMeasure period) =
      ∫ base, orientedCutLiftFlux .increasing
        (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base))
        ∂canonicalLatitudeBaseMeasure period := by
  rw [cutBulkGlobalSecondSheetOrientedCurrentIntegral_eq,
    cutBulkGlobalFirstSheetOrientedCurrentIntegral_eq,
    secondSheetOrientedScalarCurrentIntegral_eq_first]

/-- Consequently the exact global oriented boundary functional is twice its
first-sheet contribution. -/
theorem cutBulkGlobalOrientedScalarCurrentIntegral_eq_two_mul_first
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
      2 * (∫ base, orientedCutLiftFlux .increasing
        (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base))
        ∂canonicalLatitudeBaseMeasure period) := by
  rw [cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet,
    twoSheetOrientedScalarCurrentIntegral_eq_two_mul_first,
    ← cutBulkGlobalFirstSheetOrientedCurrentIntegral_eq]

/-- The positive boundary measure still records the unoriented cancellation.
This theorem is paired with the nontrivial oriented functional above so the two
roles cannot be conflated. -/
theorem cutBulkGlobalBoundaryScalarCurrent_unorientedIntegral_eq_zero
    (field test : SmoothQuotientField period hPeriod Real) :
    (∫ boundary,
        cutBulkGlobalBoundaryScalarCurrent period hPeriod field test boundary
        ∂cutBulkGlobalBoundaryCanonicalMeasure period hPeriod) = 0 :=
  integral_cutBulkGlobalBoundaryScalarCurrent_eq_zero
    period hPeriod field test

/-- Boundary-sign ledger on the exact global manifold boundary. -/
theorem cutBulkGlobalOrientedBoundaryCurrent_certificate
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
        twoSheetOrientedScalarCurrentIntegral period hPeriod field test ∧
      cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
        2 * (∫ base, orientedCutLiftFlux .increasing
          (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
            (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base))
          ∂canonicalLatitudeBaseMeasure period) ∧
      (∫ boundary,
          cutBulkGlobalBoundaryScalarCurrent period hPeriod field test boundary
          ∂cutBulkGlobalBoundaryCanonicalMeasure period hPeriod) = 0 := by
  exact ⟨cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet
      period hPeriod field test,
    cutBulkGlobalOrientedScalarCurrentIntegral_eq_two_mul_first
      period hPeriod field test,
    cutBulkGlobalBoundaryScalarCurrent_unorientedIntegral_eq_zero
      period hPeriod field test⟩

end
end P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
end JanusFormal

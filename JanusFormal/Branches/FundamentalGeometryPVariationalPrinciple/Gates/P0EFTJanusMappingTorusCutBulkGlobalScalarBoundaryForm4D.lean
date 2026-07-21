import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

/-!
# Scalar Green boundary form on the exact global cut bulk

The preceding global Green--Stokes assembly identifies the orientation-double
throat with the genuine manifold boundary of the cut-open bulk.  This file
extracts the associated scalar boundary data and packages the Green current as
an antisymmetric boundary form.

The construction is still tied to the canonical latitude collar and its two
boundary sheets.  It does not assert a symplectic structure on a completed
trace space or classify closed operator domains.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Boundary value on the first canonical sheet of the cut bulk. -/
def canonicalLatitudeScalarBoundaryValue
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeValue period hPeriod field base 0

/-- Canonical latitude-normal derivative at the first boundary sheet. -/
def canonicalLatitudeScalarBoundaryNormalDerivative
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeDerivative period hPeriod field base 0

/-- Pointwise Green boundary form on scalar boundary data. -/
def canonicalLatitudeScalarBoundaryGreenForm
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeScalarBoundaryValue period hPeriod field base *
      canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod test base -
    canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod field base *
      canonicalLatitudeScalarBoundaryValue period hPeriod test base

/-- The boundary form is exactly the previously constructed Green current at
normal coordinate zero. -/
theorem canonicalLatitudeScalarBoundaryGreenForm_eq_greenCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 := by
  rfl

/-- Pointwise antisymmetry of the scalar boundary form. -/
theorem canonicalLatitudeScalarBoundaryGreenForm_antisymm
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base =
      -canonicalLatitudeScalarBoundaryGreenForm period hPeriod test field base := by
  unfold canonicalLatitudeScalarBoundaryGreenForm
  ring

@[simp] theorem canonicalLatitudeScalarBoundaryGreenForm_self
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarBoundaryGreenForm period hPeriod field field base = 0 := by
  unfold canonicalLatitudeScalarBoundaryGreenForm
  ring

/-- Measured Green boundary form on one canonical latitude sheet. -/
def canonicalLatitudeMeasuredScalarBoundaryGreenForm
    (field test : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base, canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base
    ∂canonicalLatitudeBaseMeasure period

/-- The measured boundary form is the measured Green current at the throat. -/
theorem canonicalLatitudeMeasuredScalarBoundaryGreenForm_eq_greenCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod field test =
      canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 := by
  rfl

/-- Antisymmetry survives integration over the canonical boundary base. -/
theorem canonicalLatitudeMeasuredScalarBoundaryGreenForm_antisymm
    (field test : SmoothQuotientField period hPeriod Real) :
    canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod field test =
      -canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod test field := by
  unfold canonicalLatitudeMeasuredScalarBoundaryGreenForm
  calc
    (∫ base, canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base
        ∂canonicalLatitudeBaseMeasure period) =
        ∫ base, -canonicalLatitudeScalarBoundaryGreenForm period hPeriod test field base
          ∂canonicalLatitudeBaseMeasure period := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base =>
        canonicalLatitudeScalarBoundaryGreenForm_antisymm
          period hPeriod field test base
    _ = -(∫ base, canonicalLatitudeScalarBoundaryGreenForm period hPeriod test field base
          ∂canonicalLatitudeBaseMeasure period) := by
      rw [integral_neg]

@[simp] theorem canonicalLatitudeMeasuredScalarBoundaryGreenForm_self
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod field field = 0 := by
  unfold canonicalLatitudeMeasuredScalarBoundaryGreenForm
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarBoundaryGreenForm_self period hPeriod field base

/-- The same Green form, evaluated by the oriented functional on the genuine
manifold boundary of the global cut bulk. -/
def cutBulkGlobalScalarBoundaryGreenForm
    (field test : SmoothQuotientField period hPeriod Real) : Real :=
  cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test

/-- The genuine global boundary form is twice the first-sheet measured form.
The factor two records the two orientation-compatible boundary sheets. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_eq_two_mul_measured
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test =
      2 * canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod field test := by
  unfold cutBulkGlobalScalarBoundaryGreenForm
  rw [cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_genuineFlux,
    canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test 0 (by norm_num)]
  rfl

/-- Antisymmetry on the exact global manifold boundary. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_antisymm
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test =
      -cutBulkGlobalScalarBoundaryGreenForm period hPeriod test field := by
  rw [cutBulkGlobalScalarBoundaryGreenForm_eq_two_mul_measured,
    cutBulkGlobalScalarBoundaryGreenForm_eq_two_mul_measured,
    canonicalLatitudeMeasuredScalarBoundaryGreenForm_antisymm]
  ring

@[simp] theorem cutBulkGlobalScalarBoundaryGreenForm_self
    (field : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field field = 0 := by
  rw [cutBulkGlobalScalarBoundaryGreenForm_eq_two_mul_measured,
    canonicalLatitudeMeasuredScalarBoundaryGreenForm_self]
  ring

/-- Reusable certificate distinguishing the one-sheet, two-sheet and exact
manifold-boundary versions of the same antisymmetric form. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_certificate
    (field test : SmoothQuotientField period hPeriod Real) :
    (∀ base, canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base =
        canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0) ∧
      cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test =
        2 * canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod field test ∧
      cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test =
        -cutBulkGlobalScalarBoundaryGreenForm period hPeriod test field := by
  exact ⟨canonicalLatitudeScalarBoundaryGreenForm_eq_greenCurrent
      period hPeriod field test,
    cutBulkGlobalScalarBoundaryGreenForm_eq_two_mul_measured
      period hPeriod field test,
    cutBulkGlobalScalarBoundaryGreenForm_antisymm
      period hPeriod field test⟩

end
end P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D
end JanusFormal

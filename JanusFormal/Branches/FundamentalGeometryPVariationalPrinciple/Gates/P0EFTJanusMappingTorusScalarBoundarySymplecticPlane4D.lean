import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalScalarGreenBoundaryDomain4D

/-!
# Canonical scalar boundary symplectic plane

The global cut-bulk Green identity supplies, at every canonical boundary base
point, the value/normal-derivative pair `(phi, d_n phi)`.  This file isolates
that two-dimensional real boundary datum and its standard antisymmetric Green
form.

The construction is elementary but important: it records nondegeneracy before
any boundary condition is imposed, identifies the existing smooth Green form
with the symplectic pairing of boundary traces, and packages the corresponding
measured and exact-global boundary pairings.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarBoundarySymplecticPlane4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Value and outward-normal derivative at one canonical scalar boundary point. -/
abbrev CanonicalScalarBoundaryDatum := Real × Real

/-- Arbitrary pointwise scalar boundary data over the canonical boundary base. -/
abbrev CanonicalScalarBoundarySection :=
  CanonicalLatitudeBase → CanonicalScalarBoundaryDatum

/-- Standard antisymmetric Green form on the scalar boundary plane. -/
def canonicalScalarBoundarySymplecticForm
    (first second : CanonicalScalarBoundaryDatum) : Real :=
  first.1 * second.2 - first.2 * second.1

@[simp] theorem canonicalScalarBoundarySymplecticForm_zero_left
    (datum : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm 0 datum = 0 := by
  simp [canonicalScalarBoundarySymplecticForm]

@[simp] theorem canonicalScalarBoundarySymplecticForm_zero_right
    (datum : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm datum 0 = 0 := by
  simp [canonicalScalarBoundarySymplecticForm]

@[simp] theorem canonicalScalarBoundarySymplecticForm_add_left
    (first second third : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm (first + second) third =
      canonicalScalarBoundarySymplecticForm first third +
        canonicalScalarBoundarySymplecticForm second third := by
  simp [canonicalScalarBoundarySymplecticForm]
  ring

@[simp] theorem canonicalScalarBoundarySymplecticForm_add_right
    (first second third : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm first (second + third) =
      canonicalScalarBoundarySymplecticForm first second +
        canonicalScalarBoundarySymplecticForm first third := by
  simp [canonicalScalarBoundarySymplecticForm]
  ring

@[simp] theorem canonicalScalarBoundarySymplecticForm_smul_left
    (scalar : Real) (first second : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm (scalar • first) second =
      scalar * canonicalScalarBoundarySymplecticForm first second := by
  simp [canonicalScalarBoundarySymplecticForm]
  ring

@[simp] theorem canonicalScalarBoundarySymplecticForm_smul_right
    (scalar : Real) (first second : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm first (scalar • second) =
      scalar * canonicalScalarBoundarySymplecticForm first second := by
  simp [canonicalScalarBoundarySymplecticForm]
  ring

/-- The boundary Green form is alternating. -/
theorem canonicalScalarBoundarySymplecticForm_antisymm
    (first second : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm first second =
      -canonicalScalarBoundarySymplecticForm second first := by
  unfold canonicalScalarBoundarySymplecticForm
  ring

@[simp] theorem canonicalScalarBoundarySymplecticForm_self
    (datum : CanonicalScalarBoundaryDatum) :
    canonicalScalarBoundarySymplecticForm datum datum = 0 := by
  unfold canonicalScalarBoundarySymplecticForm
  ring

/-- The Green form detects every nonzero datum in its first argument. -/
theorem canonicalScalarBoundarySymplecticForm_nondegenerate_left
    (datum : CanonicalScalarBoundaryDatum)
    (hDatum : ∀ test : CanonicalScalarBoundaryDatum,
      canonicalScalarBoundarySymplecticForm datum test = 0) :
    datum = 0 := by
  have hValue := hDatum ((0 : Real), (1 : Real))
  have hNormal := hDatum ((1 : Real), (0 : Real))
  apply Prod.ext
  · simpa [canonicalScalarBoundarySymplecticForm] using hValue
  · change datum.2 = 0
    unfold canonicalScalarBoundarySymplecticForm at hNormal
    norm_num at hNormal
    linarith

/-- The Green form also detects every nonzero datum in its second argument. -/
theorem canonicalScalarBoundarySymplecticForm_nondegenerate_right
    (datum : CanonicalScalarBoundaryDatum)
    (hDatum : ∀ test : CanonicalScalarBoundaryDatum,
      canonicalScalarBoundarySymplecticForm test datum = 0) :
    datum = 0 := by
  apply canonicalScalarBoundarySymplecticForm_nondegenerate_left datum
  intro test
  rw [canonicalScalarBoundarySymplecticForm_antisymm]
  rw [hDatum test, neg_zero]

/-- Canonical smooth boundary datum of one quotient scalar. -/
def canonicalLatitudeScalarBoundaryDatum
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : CanonicalScalarBoundaryDatum :=
  (canonicalLatitudeScalarBoundaryValue period hPeriod field base,
    canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod field base)

/-- Boundary datum section of one smooth quotient scalar. -/
def canonicalLatitudeScalarBoundarySection
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalScalarBoundarySection :=
  fun base => canonicalLatitudeScalarBoundaryDatum period hPeriod field base

/-- The pointwise symplectic trace pairing is exactly the existing Green form. -/
theorem canonicalScalarBoundarySymplecticForm_boundaryDatum
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalScalarBoundarySymplecticForm
        (canonicalLatitudeScalarBoundaryDatum period hPeriod field base)
        (canonicalLatitudeScalarBoundaryDatum period hPeriod test base) =
      canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base := by
  rfl

/-- Measured symplectic pairing of arbitrary boundary sections. -/
def canonicalScalarBoundarySectionGreenPairing
    (first second : CanonicalScalarBoundarySection) : Real :=
  ∫ base, canonicalScalarBoundarySymplecticForm (first base) (second base)
    ∂canonicalLatitudeBaseMeasure period

/-- Exact two-sheet normalization of the canonical global boundary pairing. -/
def canonicalScalarGlobalBoundarySectionGreenPairing
    (first second : CanonicalScalarBoundarySection) : Real :=
  2 * canonicalScalarBoundarySectionGreenPairing period first second

/-- Pointwise vanishing forces the measured boundary pairing to vanish, without
an auxiliary integrability assumption. -/
theorem canonicalScalarBoundarySectionGreenPairing_eq_zero_of_pointwise
    (first second : CanonicalScalarBoundarySection)
    (hPointwise : ∀ base,
      canonicalScalarBoundarySymplecticForm (first base) (second base) = 0) :
    canonicalScalarBoundarySectionGreenPairing period first second = 0 := by
  unfold canonicalScalarBoundarySectionGreenPairing
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall hPointwise

/-- The same pointwise hypothesis kills the exact two-sheet pairing. -/
theorem canonicalScalarGlobalBoundarySectionGreenPairing_eq_zero_of_pointwise
    (first second : CanonicalScalarBoundarySection)
    (hPointwise : ∀ base,
      canonicalScalarBoundarySymplecticForm (first base) (second base) = 0) :
    canonicalScalarGlobalBoundarySectionGreenPairing period first second = 0 := by
  rw [canonicalScalarGlobalBoundarySectionGreenPairing,
    canonicalScalarBoundarySectionGreenPairing_eq_zero_of_pointwise
      period first second hPointwise]
  ring

/-- The existing one-sheet measured Green form is precisely the measured
symplectic pairing of the two smooth boundary sections. -/
theorem canonicalLatitudeMeasuredScalarBoundaryGreenForm_eq_sectionPairing
    (field test : SmoothQuotientField period hPeriod Real) :
    canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod field test =
      canonicalScalarBoundarySectionGreenPairing period
        (canonicalLatitudeScalarBoundarySection period hPeriod field)
        (canonicalLatitudeScalarBoundarySection period hPeriod test) := by
  unfold canonicalLatitudeMeasuredScalarBoundaryGreenForm
    canonicalScalarBoundarySectionGreenPairing
    canonicalLatitudeScalarBoundarySection
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base => by
    exact (canonicalScalarBoundarySymplecticForm_boundaryDatum
      period hPeriod field test base).symm

/-- The Green form on the genuine global manifold boundary is the exact
normalized symplectic pairing of the smooth trace sections. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_eq_sectionPairing
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test =
      canonicalScalarGlobalBoundarySectionGreenPairing period
        (canonicalLatitudeScalarBoundarySection period hPeriod field)
        (canonicalLatitudeScalarBoundarySection period hPeriod test) := by
  rw [cutBulkGlobalScalarBoundaryGreenForm_eq_two_mul_measured,
    canonicalLatitudeMeasuredScalarBoundaryGreenForm_eq_sectionPairing]
  rfl

/-- Nondegeneracy and exact identification certificate for the scalar boundary
plane. -/
theorem canonicalScalarBoundarySymplecticPlane_certificate
    (field test : SmoothQuotientField period hPeriod Real) :
    (∀ datum : CanonicalScalarBoundaryDatum,
        (∀ probe : CanonicalScalarBoundaryDatum,
          canonicalScalarBoundarySymplecticForm datum probe = 0) → datum = 0) ∧
      cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test =
        canonicalScalarGlobalBoundarySectionGreenPairing period
          (canonicalLatitudeScalarBoundarySection period hPeriod field)
          (canonicalLatitudeScalarBoundarySection period hPeriod test) := by
  exact ⟨canonicalScalarBoundarySymplecticForm_nondegenerate_left,
    cutBulkGlobalScalarBoundaryGreenForm_eq_sectionPairing
      period hPeriod field test⟩

end
end P0EFTJanusMappingTorusScalarBoundarySymplecticPlane4D
end JanusFormal

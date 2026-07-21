import Mathlib.MeasureTheory.Function.L2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalScalarCauchyGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D

/-!
# Physical first-sheet Hilbert Cauchy trace

The orientation-double normal derivative is a section of the normal-sign local
system.  Choosing the canonical latitude fundamental sheet trivializes that
local system over one mapping-torus period.  Both value and normal traces then
belong to the same real L2 Hilbert space over
`canonicalLatitudeBaseMeasure`.

The abstract Hilbert boundary symplectic form of these two L2 traces is proved to
be exactly the concrete first-sheet Cauchy integral appearing in the global
Green--Stokes theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
open P0EFTJanusMappingTorusCutBoundaryScalarCauchyTrace4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarCauchyGreen4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

/-- First-sheet physical scalar boundary Hilbert space. -/
abbrev CanonicalPhysicalScalarFirstSheetL2 :=
  Lp Real (2 : ENNReal) (canonicalLatitudeBaseMeasure period)

/-- First-sheet value representative. -/
def canonicalPhysicalScalarFirstSheetValue
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeValue period hPeriod field base 0

/-- First-sheet normal representative. -/
def canonicalPhysicalScalarFirstSheetNormal
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeDerivative period hPeriod field base 0

/-- Joint smoothness gives continuity of the first-sheet value. -/
theorem canonicalPhysicalScalarFirstSheetValue_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (canonicalPhysicalScalarFirstSheetValue period hPeriod field) := by
  have hParameter : Continuous
      (fun base : CanonicalLatitudeBase => (base, (0 : Real))) :=
    continuous_id.prodMk continuous_const
  exact (jointCanonicalLatitudeValue_contMDiff period hPeriod field).continuous.comp
    hParameter

/-- Joint smoothness gives continuity of the first-sheet normal derivative. -/
theorem canonicalPhysicalScalarFirstSheetNormal_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (canonicalPhysicalScalarFirstSheetNormal period hPeriod field) := by
  have hParameter : Continuous
      (fun base : CanonicalLatitudeBase => (base, (0 : Real))) :=
    continuous_id.prodMk continuous_const
  exact (jointCanonicalLatitudeDerivative_contMDiff period hPeriod field).continuous.comp
    hParameter

/-- First-sheet values are square-integrable. -/
theorem canonicalPhysicalScalarFirstSheetValue_memLp
    (field : SmoothQuotientField period hPeriod Real) :
    MemLp (canonicalPhysicalScalarFirstSheetValue period hPeriod field)
      (2 : ENNReal) (canonicalLatitudeBaseMeasure period) := by
  let value := canonicalPhysicalScalarFirstSheetValue period hPeriod field
  have hContinuous : Continuous value :=
    canonicalPhysicalScalarFirstSheetValue_continuous period hPeriod field
  apply (memLp_two_iff_integrable_sq hContinuous.aestronglyMeasurable).2
  exact continuous_integrable_canonicalLatitudeBaseMeasure period _
    (hContinuous.pow 2)

/-- First-sheet normal derivatives are square-integrable. -/
theorem canonicalPhysicalScalarFirstSheetNormal_memLp
    (field : SmoothQuotientField period hPeriod Real) :
    MemLp (canonicalPhysicalScalarFirstSheetNormal period hPeriod field)
      (2 : ENNReal) (canonicalLatitudeBaseMeasure period) := by
  let normal := canonicalPhysicalScalarFirstSheetNormal period hPeriod field
  have hContinuous : Continuous normal :=
    canonicalPhysicalScalarFirstSheetNormal_continuous period hPeriod field
  apply (memLp_two_iff_integrable_sq hContinuous.aestronglyMeasurable).2
  exact continuous_integrable_canonicalLatitudeBaseMeasure period _
    (hContinuous.pow 2)

/-- Smooth value trace into first-sheet L2. -/
def smoothCanonicalPhysicalScalarFirstSheetValueL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarFirstSheetL2 period where
  toFun field :=
    (canonicalPhysicalScalarFirstSheetValue_memLp period hPeriod field).toLp
      (canonicalPhysicalScalarFirstSheetValue period hPeriod field)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod (first + second)).coeFn_toLp,
       (canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod first).coeFn_toLp,
       (canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod second).coeFn_toLp,
       Lp.coeFn_add
        ((canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod first).toLp
            (canonicalPhysicalScalarFirstSheetValue period hPeriod first))
        ((canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod second).toLp
            (canonicalPhysicalScalarFirstSheetValue period hPeriod second))]
      with base hSum hFirst hSecond hAdd
    rw [hSum, hAdd, hFirst, hSecond]
    rfl
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards
      [(canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod (scalar • field)).coeFn_toLp,
       (canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod field).coeFn_toLp,
       Lp.coeFn_smul scalar
        ((canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod field).toLp
            (canonicalPhysicalScalarFirstSheetValue period hPeriod field))]
      with base hScaled hField hSmul
    rw [hScaled, hSmul, hField]
    rfl

/-- Smooth normal trace into first-sheet L2. -/
def smoothCanonicalPhysicalScalarFirstSheetNormalL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarFirstSheetL2 period where
  toFun field :=
    (canonicalPhysicalScalarFirstSheetNormal_memLp period hPeriod field).toLp
      (canonicalPhysicalScalarFirstSheetNormal period hPeriod field)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod (first + second)).coeFn_toLp,
       (canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod first).coeFn_toLp,
       (canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod second).coeFn_toLp,
       Lp.coeFn_add
        ((canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod first).toLp
            (canonicalPhysicalScalarFirstSheetNormal period hPeriod first))
        ((canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod second).toLp
            (canonicalPhysicalScalarFirstSheetNormal period hPeriod second))]
      with base hSum hFirst hSecond hAdd
    rw [hSum, hAdd, hFirst, hSecond]
    exact canonicalLatitudeDerivative_add
      period hPeriod first second base 0
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards
      [(canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod (scalar • field)).coeFn_toLp,
       (canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod field).coeFn_toLp,
       Lp.coeFn_smul scalar
        ((canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod field).toLp
            (canonicalPhysicalScalarFirstSheetNormal period hPeriod field))]
      with base hScaled hField hSmul
    rw [hScaled, hSmul, hField]
    exact canonicalLatitudeDerivative_smul
      period hPeriod scalar field base 0

/-- Paired first-sheet physical Cauchy trace. -/
def smoothCanonicalPhysicalScalarFirstSheetCauchyTrace :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum
        (Trace := CanonicalPhysicalScalarFirstSheetL2 period) where
  toFun field :=
    (smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field,
      smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field)
  map_add' first second := by ext <;> simp
  map_smul' scalar field := by ext <;> simp

/-- Almost-everywhere representative of the value L2 trace. -/
theorem smoothCanonicalPhysicalScalarFirstSheetValueL2_ae
    (field : SmoothQuotientField period hPeriod Real) :
    (smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field :
      CanonicalLatitudeBase → Real) =ᵐ[canonicalLatitudeBaseMeasure period]
      canonicalPhysicalScalarFirstSheetValue period hPeriod field :=
  (canonicalPhysicalScalarFirstSheetValue_memLp period hPeriod field).coeFn_toLp

/-- Almost-everywhere representative of the normal L2 trace. -/
theorem smoothCanonicalPhysicalScalarFirstSheetNormalL2_ae
    (field : SmoothQuotientField period hPeriod Real) :
    (smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field :
      CanonicalLatitudeBase → Real) =ᵐ[canonicalLatitudeBaseMeasure period]
      canonicalPhysicalScalarFirstSheetNormal period hPeriod field :=
  (canonicalPhysicalScalarFirstSheetNormal_memLp period hPeriod field).coeFn_toLp

/-- L2 value-normal inner product is the concrete latitude integral. -/
theorem inner_firstSheetValue_normal
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real
        (smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field)
        (smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod test) =
      ∫ base : CanonicalLatitudeBase,
        canonicalLatitudeValue period hPeriod field base 0 *
          canonicalLatitudeDerivative period hPeriod test base 0
        ∂canonicalLatitudeBaseMeasure period := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [smoothCanonicalPhysicalScalarFirstSheetValueL2_ae
      period hPeriod field,
     smoothCanonicalPhysicalScalarFirstSheetNormalL2_ae
      period hPeriod test]
    with base hValue hNormal
  rw [hValue, hNormal]
  simp [canonicalPhysicalScalarFirstSheetValue,
    canonicalPhysicalScalarFirstSheetNormal]

/-- L2 normal-value inner product is the second concrete latitude term. -/
theorem inner_firstSheetNormal_value
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real
        (smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field)
        (smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod test) =
      ∫ base : CanonicalLatitudeBase,
        canonicalLatitudeDerivative period hPeriod field base 0 *
          canonicalLatitudeValue period hPeriod test base 0
        ∂canonicalLatitudeBaseMeasure period := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [smoothCanonicalPhysicalScalarFirstSheetNormalL2_ae
      period hPeriod field,
     smoothCanonicalPhysicalScalarFirstSheetValueL2_ae
      period hPeriod test]
    with base hNormal hValue
  rw [hNormal, hValue]
  simp [canonicalPhysicalScalarFirstSheetValue,
    canonicalPhysicalScalarFirstSheetNormal]

/-- The Hilbert symplectic boundary form is exactly the concrete first-sheet
Cauchy pairing. -/
theorem canonicalScalarHilbertBoundarySymplecticForm_firstSheet_eq
    (field test : SmoothQuotientField period hPeriod Real) :
    canonicalScalarHilbertBoundarySymplecticForm
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod field)
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod test) =
      cutBulkGlobalFirstSheetScalarCauchyPairing
        period hPeriod field test := by
  unfold canonicalScalarHilbertBoundarySymplecticForm
  rw [inner_firstSheetValue_normal,
    inner_firstSheetNormal_value,
    cutBulkGlobalFirstSheetScalarCauchyPairing_eq_latitude,
    ← integral_sub]
  · rfl
  · exact (canonicalPhysicalScalarFirstSheetValue_memLp
      period hPeriod field).integrable_mul
        (canonicalPhysicalScalarFirstSheetNormal_memLp
          period hPeriod test)
  · exact (canonicalPhysicalScalarFirstSheetNormal_memLp
      period hPeriod field).integrable_mul
        (canonicalPhysicalScalarFirstSheetValue_memLp
          period hPeriod test)

/-- First-sheet Hilbert trace certificate. -/
theorem canonicalPhysicalScalarFirstSheetHilbertTrace_certificate
    (field test : SmoothQuotientField period hPeriod Real) :
    canonicalScalarHilbertBoundarySymplecticForm
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod field)
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod test) =
      cutBulkGlobalFirstSheetScalarCauchyPairing
        period hPeriod field test ∧
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod field)
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod test) := by
  constructor
  · exact canonicalScalarHilbertBoundarySymplecticForm_firstSheet_eq
      period hPeriod field test
  · rw [canonicalScalarHilbertBoundarySymplecticForm_firstSheet_eq]
    exact cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_cauchyPairing
      period hPeriod field test

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
end JanusFormal

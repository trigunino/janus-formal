import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffScalarCurrent4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
set_option autoImplicit false
noncomputable section
open scoped Interval
open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffScalarCurrent4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Scalar coefficient of the current density for the product collar measure
`canonicalLatitudeBaseMeasure × volume(normal)`. -/
def cutoffCollarScalarCurrentDensity
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeCollarCutoff normal *
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal

/-- Normal-coordinate divergence density.  The throat-base volume factor is
represented by integration against `canonicalLatitudeBaseMeasure`. -/
def cutoffCollarScalarCurrentDensitizedDivergence
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  cutoffLatitudeScalarCurrentCoordinateDivergence period hPeriod massSquared
    field test base normal

theorem cutoffCollarScalarCurrentDensity_hasDerivAt
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    HasDerivAt
      (cutoffCollarScalarCurrentDensity period hPeriod field test base)
      (cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test base normal) normal :=
  cutoffLatitudeScalarCurrent_hasDerivAt period hPeriod massSquared
    field test base normal

theorem cutoffCollarScalarCurrentDensity_boundary_neg_one
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutoffCollarScalarCurrentDensity period hPeriod field test base (-1) = 0 := by
  rw [cutoffCollarScalarCurrentDensity,
    canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs (-1) (by norm_num),
    zero_mul]

theorem cutoffCollarScalarCurrentDensity_boundary_one
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutoffCollarScalarCurrentDensity period hPeriod field test base 1 = 0 := by
  rw [cutoffCollarScalarCurrentDensity,
    canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs 1 (by norm_num),
    zero_mul]

/-- One-fiber Stokes formula for the compactly supported local current. -/
theorem intervalIntegral_cutoffCollarScalarCurrentDivergence_eq_zero
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    ∫ normal in (-1 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal = 0 := by
  have hValue (f : SmoothQuotientField period hPeriod Real) :
      Continuous (canonicalLatitudeValue period hPeriod f base) :=
    continuous_iff_continuousAt.mpr fun normal =>
      (canonicalLatitudeValue_hasDerivAt period hPeriod f base normal).continuousAt
  have hDerivative (f : SmoothQuotientField period hPeriod Real) :
      Continuous (canonicalLatitudeDerivative period hPeriod f base) :=
    (canonicalLatitudeDerivative_contDiff period hPeriod f base).continuous
  have hResidual (f : SmoothQuotientField period hPeriod Real) :
      Continuous (canonicalLatitudeScalarEulerResidual period hPeriod massSquared f base) := by
    unfold canonicalLatitudeScalarEulerResidual
    exact (canonicalLatitudeSecondDerivative_continuous period hPeriod f base).add
      (continuous_const.mul (hValue f))
  have hGreen : Continuous
      (canonicalLatitudeScalarGreenCurrent period hPeriod field test base) := by
    unfold canonicalLatitudeScalarGreenCurrent
    exact ((hValue field).mul (hDerivative test)).sub
      ((hDerivative field).mul (hValue test))
  have hCut : Continuous canonicalLatitudeCollarCutoff :=
    canonicalLatitudeCollarCutoff_contDiff.continuous
  have hCutDeriv : Continuous (deriv canonicalLatitudeCollarCutoff) :=
    canonicalLatitudeCollarCutoff_contDiff.continuous_deriv (by simp)
  have hDivergence : Continuous
      (cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test base) := by
    unfold cutoffCollarScalarCurrentDensitizedDivergence
      cutoffLatitudeScalarCurrentCoordinateDivergence
    exact (hCutDeriv.mul hGreen).add (hCut.mul
      (((hValue field).mul (hResidual test)).sub
        ((hResidual field).mul (hValue test))))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := cutoffCollarScalarCurrentDensity period hPeriod field test base)
    (f' := cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
      field test base)
    (a := (-1 : Real)) (b := 1)
    (fun normal _ => cutoffCollarScalarCurrentDensity_hasDerivAt period hPeriod
      massSquared field test base normal)
    (hDivergence.intervalIntegrable (-1) 1)
  rw [hFTC, cutoffCollarScalarCurrentDensity_boundary_one,
    cutoffCollarScalarCurrentDensity_boundary_neg_one, sub_zero]

/-- Iterated product-measure form of local Stokes on the cutoff collar. -/
theorem productCollarIntegral_cutoffCurrentDivergence_eq_zero
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ base, (∫ normal in (-1 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal) ∂(canonicalLatitudeBaseMeasure period) = 0 := by
  simp only [intervalIntegral_cutoffCollarScalarCurrentDivergence_eq_zero]
  simp

end
end P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
end JanusFormal

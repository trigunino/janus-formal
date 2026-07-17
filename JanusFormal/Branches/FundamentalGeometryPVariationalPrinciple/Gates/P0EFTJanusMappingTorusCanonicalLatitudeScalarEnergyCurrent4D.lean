import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D

/-!
# Conserved scalar energy on the canonical latitude collar

The autonomous equal-mass collar equation has the exact first integral
`(phi')^2 + m^2 phi^2`.  This is a one-dimensional stress-energy conservation
law on the canonical collar; no global four-dimensional divergence theorem is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeScalarEnergyCurrent4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D

/-- Twice the standard one-dimensional scalar energy density. -/
def canonicalLatitudeScalarEnergyCurrent
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeDerivative period hPeriod field base normal ^ 2 +
    massSquared *
      canonicalLatitudeValue period hPeriod field base normal ^ 2

/-- The normal derivative of the energy is twice `phi'` times the exact
collar Euler residual. -/
theorem canonicalLatitudeScalarEnergyCurrent_hasDerivAt
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    CanonicalLatitudeScalarHasDerivAt
      (canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base)
      (2 * canonicalLatitudeDerivative period hPeriod field base normal *
        canonicalLatitudeScalarEulerResidual period hPeriod massSquared field
          base normal)
      normal := by
  unfold CanonicalLatitudeScalarHasDerivAt
  have hDerivative :=
    canonicalLatitudeDerivative_hasDerivAt period hPeriod field base normal
  have hValue :=
    canonicalLatitudeValue_hasDerivAt period hPeriod field base normal
  have hRaw :=
    (hDerivative.mul hDerivative).add ((hValue.mul hValue).const_mul massSquared)
  convert hRaw using 1
  · funext current
    simp [canonicalLatitudeScalarEnergyCurrent, pow_two]
  · simp only [canonicalLatitudeScalarEulerResidual]
    ring

theorem canonicalLatitudeScalarEnergyCurrent_hasDerivAt_zero_of_euler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (base : CanonicalLatitudeBase) (normal : Real) :
    CanonicalLatitudeScalarHasDerivAt
      (canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base)
      0 normal := by
  simpa [hField base normal] using
    (canonicalLatitudeScalarEnergyCurrent_hasDerivAt period hPeriod massSquared
      field base normal)

/-- The scalar energy is constant between arbitrary normal coordinates on one
canonical latitude fiber. -/
theorem canonicalLatitudeScalarEnergyCurrent_eq_of_euler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (base : CanonicalLatitudeBase) (first second : Real) :
    canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base first =
      canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base second := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := first) (b := second)
    (f := canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base)
    (f' := fun _ : Real => 0)
    (fun normal _ => by
      have hZero :=
        canonicalLatitudeScalarEnergyCurrent_hasDerivAt_zero_of_euler period
          hPeriod massSquared field hField base normal
      unfold CanonicalLatitudeScalarHasDerivAt at hZero
      exact hZero)
    (continuous_const.intervalIntegrable first second)
  have hDifference :
      canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base second -
        canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base first = 0 := by
    simpa using hFTC.symm
  linarith

theorem canonicalLatitudeScalarEnergyCurrent_endpointJump_zero_of_euler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base 1 -
        canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base 0 = 0 := by
  rw [canonicalLatitudeScalarEnergyCurrent_eq_of_euler period hPeriod massSquared
    field hField base 1 0]
  ring

theorem canonicalLatitudeScalarEnergyCurrent_nonneg
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (hMass : 0 ≤ massSquared)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    0 ≤ canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field
      base normal := by
  unfold canonicalLatitudeScalarEnergyCurrent
  positivity

/-- Energy integrated over the same canonical throat-base measure as the
collar IPP and Green-current gates. -/
def canonicalLatitudeMeasuredScalarEnergyCurrent
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (normal : Real) : Real :=
  ∫ base,
    canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base normal
    ∂(canonicalLatitudeBaseMeasure period)

theorem canonicalLatitudeMeasuredScalarEnergyCurrent_eq_of_euler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (first second : Real) :
    canonicalLatitudeMeasuredScalarEnergyCurrent period hPeriod massSquared field first =
      canonicalLatitudeMeasuredScalarEnergyCurrent period hPeriod massSquared field second := by
  unfold canonicalLatitudeMeasuredScalarEnergyCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarEnergyCurrent_eq_of_euler period hPeriod massSquared
      field hField base first second

end

end P0EFTJanusMappingTorusCanonicalLatitudeScalarEnergyCurrent4D
end JanusFormal

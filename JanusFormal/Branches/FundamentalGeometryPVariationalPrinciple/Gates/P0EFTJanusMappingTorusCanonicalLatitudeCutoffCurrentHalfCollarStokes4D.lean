import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLatitudeCutoffCurrentZeroExtensionPrerequisite4D

/-! # Exact cutoff-current Stokes formula on the positive half-collar -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentHalfCollarStokes4D

set_option autoImplicit false
noncomputable section

open scoped Interval
open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusLatitudeCutoffCurrentZeroExtensionPrerequisite4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem cutoffCollarScalarCurrentDensity_boundary_zero
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutoffCollarScalarCurrentDensity period hPeriod field test base 0 =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 := by
  rw [cutoffCollarScalarCurrentDensity,
    canonicalLatitudeCollarCutoff_eq_one 0 (by norm_num), one_mul]

/-- One-fiber Green–Stokes formula on the positive cut collar. The artificial
outer face vanishes by the cutoff; only the outward throat flux remains. -/
theorem intervalIntegral_cutoffCurrentDivergence_eq_neg_throatFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    ∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal =
      -canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 := by
  have hDensity :=
    cutoffCollarScalarCurrentDensity_contDiff period hPeriod field test base
  have hDivergence :
      cutoffCollarScalarCurrentDensitizedDivergence period hPeriod
        massSquared field test base =
      deriv (cutoffCollarScalarCurrentDensity period hPeriod field test base) := by
    funext normal
    exact (cutoffCollarScalarCurrentDensity_hasDerivAt period hPeriod
      massSquared field test base normal).deriv.symm
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := cutoffCollarScalarCurrentDensity period hPeriod field test base)
    (f' := cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
      field test base)
    (a := (0 : Real)) (b := 1)
    (fun normal _ => cutoffCollarScalarCurrentDensity_hasDerivAt period hPeriod
      massSquared field test base normal)
    (by rw [hDivergence]
        exact (hDensity.continuous_deriv (by simp)).intervalIntegrable 0 1)
  rw [hFTC, cutoffCollarScalarCurrentDensity_boundary_one,
    cutoffCollarScalarCurrentDensity_boundary_zero, zero_sub]

/-- Product-measure form: the positive half-collar divergence is exactly the
negative measured throat current. -/
theorem productHalfCollarIntegral_cutoffCurrentDivergence_eq_neg_throatFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ base, (∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal) ∂(canonicalLatitudeBaseMeasure period) =
      -canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 := by
  unfold canonicalLatitudeMeasuredScalarGreenCurrent
  simp only [intervalIntegral_cutoffCurrentDivergence_eq_neg_throatFlux,
    integral_neg]

end
end P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentHalfCollarStokes4D
end JanusFormal

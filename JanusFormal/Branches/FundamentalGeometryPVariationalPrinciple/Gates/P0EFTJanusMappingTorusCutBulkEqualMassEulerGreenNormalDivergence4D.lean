import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D

/-!
# Equal-mass Euler reduction of the genuine normal divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffScalarCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- On two equal-mass collar Euler solutions, the genuine normal divergence
density is purely the cutoff derivative times the true intrinsic flux. -/
theorem canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_cutoffDerivative_mul_flux_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (parameter : CanonicalLatitudeCollarParameter)
    (hNormal : parameter.2 ∈ Set.Icc (0 : Real) 1) :
    canonicalCutBulkGenuineGreenNormalDivergenceDensity period hPeriod
        massSquared field test parameter =
      deriv canonicalLatitudeCollarCutoff parameter.2 *
        canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test
          parameter.1 parameter.2 := by
  rw [canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_canonical]
  unfold canonicalCutBulkDivergenceDensity
    cutoffCollarScalarCurrentDensitizedDivergence
    cutoffLatitudeScalarCurrentCoordinateDivergence
  rw [hField parameter.1 parameter.2, hTest parameter.1 parameter.2]
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  rw [canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
    period hPeriod field test parameter.1 parameter.2 hNormal]

/-- In the core collar, where the cutoff is constant, the on-shell genuine
normal divergence density vanishes exactly. -/
theorem canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_zero_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (parameter : CanonicalLatitudeCollarParameter)
    (hNormal : |parameter.2| < 1 / 2) :
    canonicalCutBulkGenuineGreenNormalDivergenceDensity period hPeriod
      massSquared field test parameter = 0 := by
  rw [canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_canonical]
  unfold canonicalCutBulkDivergenceDensity
    cutoffCollarScalarCurrentDensitizedDivergence
  rw [cutoffLatitudeScalarCurrentCoordinateDivergence_eq_green
      period hPeriod massSquared field test parameter.1 parameter.2 hNormal,
    hField parameter.1 parameter.2, hTest parameter.1 parameter.2]
  simp

end
end P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D
end JanusFormal

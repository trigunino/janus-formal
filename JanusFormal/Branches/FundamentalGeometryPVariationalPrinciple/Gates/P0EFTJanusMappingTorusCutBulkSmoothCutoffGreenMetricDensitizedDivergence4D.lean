import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenNormalDivergenceMeasure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D

/-!
# Metric-densitized divergence of the global cutoff Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenNormalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Coordinate density of the covariant divergence with respect to the
canonical latitude product coordinates. The factor `cos²(normal)` is the
proved metric-volume Jacobian. -/
def canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  deriv canonicalPositiveLatitudeWeight parameter.2 *
      canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test
        parameter.1 parameter.2 +
    canonicalPositiveLatitudeWeight parameter.2 *
      canonicalCutBulkDivergenceDensity period hPeriod massSquared field test parameter

private theorem canonicalPositiveLatitudeWeight_contDiff :
    ContDiff Real ∞ canonicalPositiveLatitudeWeight := by
  unfold canonicalPositiveLatitudeWeight
  exact Real.contDiff_cos.pow 2

/-- Actual product rule for the metric-densitized normal flux
`cos²(normal) · g(χJ, normal)`. -/
theorem canonicalCutBulkSmoothCutoffGreenMetricFlux_hasDerivAt
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    HasDerivAt
      (fun current => canonicalPositiveLatitudeWeight current *
        canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test
          base current)
      (canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test (base, normal)) normal := by
  have hWeight : HasDerivAt canonicalPositiveLatitudeWeight
      (deriv canonicalPositiveLatitudeWeight normal) normal :=
    (canonicalPositiveLatitudeWeight_contDiff.differentiable
      (by simp)).differentiableAt.hasDerivAt
  exact hWeight.mul
    (canonicalCutBulkSmoothCutoffGreenNormalFlux_hasDerivAt period hPeriod
      massSquared field test base normal hNormal)

theorem deriv_canonicalCutBulkSmoothCutoffGreenMetricFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    deriv (fun current => canonicalPositiveLatitudeWeight current *
        canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test
          base current) normal =
      canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test (base, normal) :=
  (canonicalCutBulkSmoothCutoffGreenMetricFlux_hasDerivAt period hPeriod
    massSquared field test base normal hNormal).deriv

/-- Exact correction to the unweighted normal-divergence density. -/
theorem canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_jacobian_correction
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test parameter =
      deriv canonicalPositiveLatitudeWeight parameter.2 *
          canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test
            parameter.1 parameter.2 +
        canonicalPositiveLatitudeWeight parameter.2 *
          canonicalCutBulkGenuineGreenNormalDivergenceDensity period hPeriod
            massSquared field test parameter := by
  unfold canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence
  rw [canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_canonical]

/-- On equal-mass Euler solutions, the metric density is the exact derivative
of `cos² · cutoff` times the genuine intrinsic normal flux. -/
theorem canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_weightedCutoffDerivative_mul_flux_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test (base, normal) =
      (deriv canonicalPositiveLatitudeWeight normal *
          canonicalLatitudeCollarCutoff normal +
        canonicalPositiveLatitudeWeight normal *
          deriv canonicalLatitudeCollarCutoff normal) *
        canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test
          base normal := by
  rw [canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_jacobian_correction,
    canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_cutoffDerivative_mul_flux_of_euler
      period hPeriod massSquared field test hField hTest (base, normal)
        ⟨hNormal.1.le, hNormal.2.le⟩,
    canonicalCutBulkSmoothCutoffGreenNormalFlux_eq_scalarCurrent
      period hPeriod field test base normal ⟨hNormal.1.le, hNormal.2.le⟩,
    cutBulkScalarCurrent_canonicalCollarPath_eq_cutoff_mul_intrinsicFlux
      period hPeriod field test base normal ⟨hNormal.1.le, hNormal.2.le⟩]
  ring

end
end P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarDerivative4D

/-!
# Tangential compensation required by the metric Jacobian
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The tangential term which cancels the logarithmic derivative of the
metric-volume Jacobian in a conserved four-dimensional Green current. -/
def canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  -(deriv canonicalPositiveLatitudeWeight normal /
      canonicalPositiveLatitudeWeight normal *
    canonicalLatitudeCollarCutoff normal *
    canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test
      base normal)

/-- Under the established latitude Euler equations, adding precisely the
tangential Jacobian compensation to the normal metric divergence leaves the
genuine cutoff-gradient flux required by the local covariant Leibniz rule. -/
theorem metricNormalDivergence_add_tangentialCompensation_eq_cutoffGradientFlux_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence period hPeriod
        massSquared field test (base, normal) +
      canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation period hPeriod
        field test base normal =
      deriv canonicalLatitudeCollarCutoff normal *
        canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test
          base normal := by
  rw [canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence_eq_of_euler
    period hPeriod massSquared field test hField hTest base normal hNormal]
  unfold canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation
  have hWeight : canonicalPositiveLatitudeWeight normal ≠ 0 :=
    ne_of_gt (canonicalPositiveLatitudeWeight_pos_of_mem_Icc normal
      ⟨hNormal.1.le, hNormal.2.le⟩)
  field_simp [hWeight]
  ring

theorem metricDensitizedDivergence_add_weightedTangentialCompensation_eq_weightedCutoffGradientFlux_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test (base, normal) +
      canonicalPositiveLatitudeWeight normal *
        canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation period hPeriod
          field test base normal =
      canonicalPositiveLatitudeWeight normal *
        deriv canonicalLatitudeCollarCutoff normal *
          canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test
            base normal := by
  rw [← canonicalPositiveLatitudeWeight_mul_metricNormalDivergence
    period hPeriod massSquared field test (base, normal)
      ⟨hNormal.1.le, hNormal.2.le⟩,
    ← mul_add]
  rw [metricNormalDivergence_add_tangentialCompensation_eq_cutoffGradientFlux_of_euler
    period hPeriod massSquared field test hField hTest base normal hNormal]
  ring

end
end P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D
end JanusFormal

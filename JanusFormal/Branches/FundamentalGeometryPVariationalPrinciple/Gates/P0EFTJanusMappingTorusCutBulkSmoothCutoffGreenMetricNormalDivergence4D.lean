import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDivergenceMeasure4D

/-!
# Undensitized metric-normal divergence of the global cutoff Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem canonicalPositiveLatitudeWeight_pos_of_mem_Icc
    (normal : Real) (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    0 < canonicalPositiveLatitudeWeight normal := by
  rcases hNormal with ⟨hZero, hOne⟩
  have hAngle : normal ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_gt_three]
  unfold canonicalPositiveLatitudeWeight
  exact sq_pos_of_pos (Real.cos_pos_of_mem_Ioo hAngle)

/-- The normal contribution to the covariant divergence, obtained by dividing
the proved metric-volume density by its positive Jacobian. Tangential
divergence is deliberately not included. -/
def canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
    massSquared field test parameter /
      canonicalPositiveLatitudeWeight parameter.2

theorem canonicalPositiveLatitudeWeight_mul_metricNormalDivergence
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter)
    (hNormal : parameter.2 ∈ Set.Icc (0 : Real) 1) :
    canonicalPositiveLatitudeWeight parameter.2 *
        canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence period hPeriod
          massSquared field test parameter =
      canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test parameter := by
  unfold canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence
  field_simp [ne_of_gt (canonicalPositiveLatitudeWeight_pos_of_mem_Icc
    parameter.2 hNormal)]

theorem canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence_eq_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence period hPeriod
        massSquared field test (base, normal) =
      ((deriv canonicalPositiveLatitudeWeight normal *
            canonicalLatitudeCollarCutoff normal +
          canonicalPositiveLatitudeWeight normal *
            deriv canonicalLatitudeCollarCutoff normal) /
        canonicalPositiveLatitudeWeight normal) *
          canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test
            base normal := by
  unfold canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence
  rw [canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_weightedCutoffDerivative_mul_flux_of_euler
    period hPeriod massSquared field test hField hTest base normal hNormal]
  ring

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

/-- The same pushed measure, now written as metric Jacobian times the
undensitized normal contribution. -/
def cutBulkSmoothCutoffGreenMetricNormalDivergenceMeasure
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    VectorMeasure (PositiveHemisphereCutBulk period hPeriod) Real :=
  ((canonicalLatitudeCollarMeasure period).withDensityᵥ
      (fun parameter ↦ canonicalPositiveLatitudeWeight parameter.2 *
        canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence period hPeriod
          massSquared field test parameter)).map
    (canonicalLatitudeCutBulkCollarMap period hPeriod)

theorem cutBulkSmoothCutoffGreenMetricNormalDivergenceMeasure_eq_metric
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkSmoothCutoffGreenMetricNormalDivergenceMeasure period hPeriod
        massSquared field test =
      cutBulkSmoothCutoffGreenMetricDivergenceMeasure period hPeriod
        massSquared field test := by
  unfold cutBulkSmoothCutoffGreenMetricNormalDivergenceMeasure
    cutBulkSmoothCutoffGreenMetricDivergenceMeasure
  congr 1
  apply WithDensityᵥEq.congr_ae
  rw [canonicalLatitudeCollarMeasure]
  have hSupport : ∀ᵐ parameter
      ∂(canonicalLatitudeBaseMeasure period).prod canonicalLatitudeUnitNormalMeasure,
      parameter.2 ∈ Set.Icc (0 : Real) 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Icc.preimage measurable_snd)).2
    filter_upwards [] with base
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with normal hNormal
    exact Set.Ioc_subset_Icc_self hNormal
  filter_upwards [hSupport] with parameter hNormal
  exact canonicalPositiveLatitudeWeight_mul_metricNormalDivergence
    period hPeriod massSquared field test parameter hNormal

theorem two_mul_cutBulkSmoothCutoffGreenMetricNormalDivergenceMeasure_univ_eq_neg_flux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkSmoothCutoffGreenMetricNormalDivergenceMeasure period hPeriod
        massSquared field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [cutBulkSmoothCutoffGreenMetricNormalDivergenceMeasure_eq_metric,
    two_mul_cutBulkSmoothCutoffGreenMetricDivergenceMeasure_univ_eq_neg_flux]

end
end P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D
end JanusFormal

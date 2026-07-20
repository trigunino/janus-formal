import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D

/-!
# Metric divergence measure of the global cutoff Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDivergenceMeasure4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentHalfCollarStokes4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointDivergenceSmooth4D
open P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenNormalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private def jointMetricDensitizedDivergence
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  deriv canonicalPositiveLatitudeWeight parameter.2 *
      jointCutoffCollarScalarCurrentDensity period hPeriod field test parameter +
    canonicalPositiveLatitudeWeight parameter.2 *
      jointCutoffCollarScalarCurrentDivergence period hPeriod field test parameter

private theorem jointMetricDensitizedDivergence_continuous
    (field test : SmoothQuotientField period hPeriod Real) :
    Continuous (jointMetricDensitizedDivergence period hPeriod field test) := by
  have hWeightSmooth : ContDiff Real ∞ canonicalPositiveLatitudeWeight := by
    unfold canonicalPositiveLatitudeWeight
    exact Real.contDiff_cos.pow 2
  have hWeight : Continuous canonicalPositiveLatitudeWeight :=
    hWeightSmooth.continuous
  have hWeightDeriv : Continuous (deriv canonicalPositiveLatitudeWeight) :=
    hWeightSmooth.continuous_deriv (by simp)
  exact ((hWeightDeriv.comp continuous_snd).mul
      (jointCutoffCollarScalarCurrentDensity_contMDiff
        period hPeriod field test).continuous).add
    ((hWeight.comp continuous_snd).mul
      (jointCutoffCollarScalarCurrentDivergence_contMDiff
        period hPeriod field test).continuous)

theorem canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_joint
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter)
    (hNormal : parameter.2 ∈ Set.Icc (0 : Real) 1) :
    canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test parameter =
      jointMetricDensitizedDivergence period hPeriod field test parameter := by
  unfold canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence
    jointMetricDensitizedDivergence canonicalCutBulkDivergenceDensity
  rw [canonicalCutBulkSmoothCutoffGreenNormalFlux_eq_scalarCurrent
      period hPeriod field test parameter.1 parameter.2 hNormal,
    cutBulkScalarCurrent_canonicalCollarPath,
    Set.projIcc_of_mem zero_le_one hNormal,
    jointCutoffCollarScalarCurrentDensity_eq,
    jointCutoffCollarScalarCurrentDivergence_eq period hPeriod massSquared]

theorem canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_integrable
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    Integrable
      (canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test)
      (canonicalLatitudeCollarMeasure period) := by
  let jointDensity := jointMetricDensitizedDivergence period hPeriod field test
  have hContinuous : Continuous jointDensity :=
    jointMetricDensitizedDivergence_continuous period hPeriod field test
  have hFiber (base : CanonicalLatitudeBase) : Integrable
      (fun normal ↦ jointDensity (base, normal))
      canonicalLatitudeUnitNormalMeasure := by
    have hFiberContinuous : Continuous (fun normal ↦ jointDensity (base, normal)) :=
      hContinuous.comp (continuous_const.prodMk continuous_id)
    unfold canonicalLatitudeUnitNormalMeasure
    have hIcc : Integrable (fun normal ↦ jointDensity (base, normal))
        (volume.restrict (Set.Icc (0 : Real) 1)) :=
      hFiberContinuous.continuousOn.integrableOn_Icc
    exact hIcc.mono_measure
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  have hInnerInterval : Continuous (fun base : CanonicalLatitudeBase ↦
      ∫ normal in (0 : Real)..1, ‖jointDensity (base, normal)‖) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hContinuous.norm
  have hInner : Continuous (fun base : CanonicalLatitudeBase ↦
      ∫ normal, ‖jointDensity (base, normal)‖
        ∂canonicalLatitudeUnitNormalMeasure) := by
    apply hInnerInterval.congr
    intro base
    rw [intervalIntegral.integral_of_le zero_le_one]
    rfl
  have hJointIntegrable : Integrable jointDensity
      ((canonicalLatitudeBaseMeasure period).prod
        canonicalLatitudeUnitNormalMeasure) := by
    refine (integrable_prod_iff hContinuous.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall hFiber
    · exact continuous_integrable_canonicalLatitudeBaseMeasure period _ hInner
  rw [canonicalLatitudeCollarMeasure]
  apply hJointIntegrable.congr
  have hSupport : ∀ᵐ parameter
      ∂(canonicalLatitudeBaseMeasure period).prod canonicalLatitudeUnitNormalMeasure,
      parameter.2 ∈ Set.Icc (0 : Real) 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Icc.preimage measurable_snd)).2
    filter_upwards [] with base
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with normal hNormal
    exact Set.Ioc_subset_Icc_self hNormal
  filter_upwards [hSupport] with parameter hNormal
  exact (canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_joint
    period hPeriod massSquared field test parameter hNormal).symm

private theorem weightedCutoffCurrent_hasDerivAt
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    HasDerivAt
      (canonicalPositiveLatitudeWeight *
        cutoffCollarScalarCurrentDensity period hPeriod field test base)
      (jointMetricDensitizedDivergence period hPeriod field test (base, normal))
      normal := by
  have hWeight : HasDerivAt canonicalPositiveLatitudeWeight
      (deriv canonicalPositiveLatitudeWeight normal) normal := by
    have hSmooth : ContDiff Real ∞ canonicalPositiveLatitudeWeight := by
      unfold canonicalPositiveLatitudeWeight
      exact Real.contDiff_cos.pow 2
    exact (hSmooth.differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hProduct : HasDerivAt
      (canonicalPositiveLatitudeWeight *
        cutoffCollarScalarCurrentDensity period hPeriod field test base)
      (deriv canonicalPositiveLatitudeWeight normal *
          cutoffCollarScalarCurrentDensity period hPeriod field test base normal +
        canonicalPositiveLatitudeWeight normal *
          cutoffCollarScalarCurrentDensitizedDivergence period hPeriod
            massSquared field test base normal) normal := by
    simpa only [Pi.mul_apply] using hWeight.mul
      (cutoffCollarScalarCurrentDensity_hasDerivAt period hPeriod
        massSquared field test base normal)
  convert hProduct using 1
  simp only [jointMetricDensitizedDivergence,
    jointCutoffCollarScalarCurrentDensity_eq,
    jointCutoffCollarScalarCurrentDivergence_eq period hPeriod massSquared]

theorem intervalIntegral_metricDensitizedDivergence_eq_neg_throatFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    ∫ normal in (0 : Real)..1,
        canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
          massSquared field test (base, normal) =
      -canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 := by
  let jointDensity : Real → Real := fun normal ↦
    jointMetricDensitizedDivergence period hPeriod field test (base, normal)
  have hContinuous : Continuous jointDensity :=
    (jointMetricDensitizedDivergence_continuous period hPeriod field test).comp
      (continuous_const.prodMk continuous_id)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := canonicalPositiveLatitudeWeight *
      cutoffCollarScalarCurrentDensity period hPeriod field test base)
    (f' := jointDensity) (a := (0 : Real)) (b := 1)
    (fun normal _ ↦ weightedCutoffCurrent_hasDerivAt period hPeriod massSquared
      field test base normal)
    (hContinuous.intervalIntegrable 0 1)
  calc
    _ = ∫ normal in (0 : Real)..1, jointDensity normal := by
      apply intervalIntegral.integral_congr
      intro normal hNormal
      rw [Set.uIcc_of_le zero_le_one] at hNormal
      exact canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_joint
        period hPeriod massSquared field test (base, normal)
          hNormal
    _ = _ := by
      rw [hFTC]
      simp only [Pi.mul_apply]
      rw [cutoffCollarScalarCurrentDensity_boundary_one,
        cutoffCollarScalarCurrentDensity_boundary_zero]
      simp [canonicalPositiveLatitudeWeight]

theorem productHalfCollarIntegral_metricDensitizedDivergence_eq_neg_throatFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ base, (∫ normal in (0 : Real)..1,
        canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
          massSquared field test (base, normal))
        ∂canonicalLatitudeBaseMeasure period =
      -canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 := by
  unfold canonicalLatitudeMeasuredScalarGreenCurrent
  simp only [intervalIntegral_metricDensitizedDivergence_eq_neg_throatFlux,
    integral_neg]

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

def cutBulkSmoothCutoffGreenMetricDivergenceMeasure
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    VectorMeasure (PositiveHemisphereCutBulk period hPeriod) Real :=
  ((canonicalLatitudeCollarMeasure period).withDensityᵥ
      (canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test)).map
    (canonicalLatitudeCutBulkCollarMap period hPeriod)

theorem cutBulkSmoothCutoffGreenMetricDivergenceMeasure_univ
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkSmoothCutoffGreenMetricDivergenceMeasure period hPeriod
        massSquared field test Set.univ =
      ∫ base, (∫ normal in (0 : Real)..1,
        canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
          massSquared field test (base, normal))
        ∂canonicalLatitudeBaseMeasure period := by
  letI : IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
    canonicalLatitudeBaseMeasure_isFinite period
  have hIntegrable :=
    canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_integrable
      period hPeriod massSquared field test
  rw [cutBulkSmoothCutoffGreenMetricDivergenceMeasure, VectorMeasure.map_apply _
    (continuous_canonicalLatitudeCutBulkCollarMap period hPeriod).measurable
      MeasurableSet.univ]
  rw [Set.preimage_univ, withDensityᵥ_apply hIntegrable MeasurableSet.univ,
    setIntegral_univ, canonicalLatitudeCollarMeasure]
  have hIntegrable' := hIntegrable
  change Integrable
      (Function.uncurry (fun base : CanonicalLatitudeBase ↦ fun normal : Real ↦
        canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
          massSquared field test (base, normal)))
      ((canonicalLatitudeBaseMeasure period).prod
        canonicalLatitudeUnitNormalMeasure) at hIntegrable'
  calc
    (∫ parameter : CanonicalLatitudeCollarParameter,
        canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
          massSquared field test parameter
        ∂(canonicalLatitudeBaseMeasure period).prod
          canonicalLatitudeUnitNormalMeasure) =
      ∫ base, (∫ normal,
        canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
          massSquared field test (base, normal)
        ∂canonicalLatitudeUnitNormalMeasure)
        ∂canonicalLatitudeBaseMeasure period := by
          simpa [Function.uncurry] using (integral_integral hIntegrable').symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base ↦ by
        change (∫ normal,
            canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
              massSquared field test (base, normal)
            ∂canonicalLatitudeUnitNormalMeasure) =
          ∫ normal in (0 : Real)..1,
            canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
              massSquared field test (base, normal)
        rw [intervalIntegral.integral_of_le zero_le_one]
        rfl

theorem two_mul_cutBulkSmoothCutoffGreenMetricDivergenceMeasure_univ_eq_neg_flux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkSmoothCutoffGreenMetricDivergenceMeasure period hPeriod
        massSquared field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [cutBulkSmoothCutoffGreenMetricDivergenceMeasure_univ,
    productHalfCollarIntegral_metricDensitizedDivergence_eq_neg_throatFlux,
    canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test 0 (by norm_num)]
  ring

end
end P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDivergenceMeasure4D
end JanusFormal

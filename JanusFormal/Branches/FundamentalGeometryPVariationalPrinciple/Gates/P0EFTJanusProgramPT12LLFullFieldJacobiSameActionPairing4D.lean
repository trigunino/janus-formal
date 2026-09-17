import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullFieldJacobiL2Core4D

/-! # PT pairing of the complete smooth LL Jacobi field row -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullFieldJacobiSameActionPairing4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLFullFieldJacobiL2Core4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

theorem pt_pullback_aux_plus
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) :
    llPTPullback period hPeriod (auxPlusFields period hPeriod fields dAux) =
      auxPlusFields period hPeriod (llPTPullback period hPeriod fields)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux) := by
  cases fields
  simp only [llPTPullback, auxPlusFields, differentialLLAuxMetricDirectionPT]
  congr 1

theorem pt_pullback_aux_minus
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) :
    llPTPullback period hPeriod (auxMinusFields period hPeriod fields dAux) =
      auxMinusFields period hPeriod (llPTPullback period hPeriod fields)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux) := by
  cases fields
  simp only [llPTPullback, auxMinusFields, differentialLLAuxMetricDirectionPT]
  congr 1

theorem pt_pullback_measure_plus
    (fields : IndependentFields period hPeriod)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    llPTPullback period hPeriod (measurePlusFields period hPeriod fields dMeasure) =
      measurePlusFields period hPeriod (llPTPullback period hPeriod fields)
        (throatPTPullback period hPeriod Real dMeasure) := by
  cases fields
  simp only [llPTPullback, measurePlusFields]
  congr 1

private theorem raw_worldvolume_pt_point
    (fields : IndependentFields period hPeriod)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField testField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    llWorldvolumeHessianDensity period hPeriod
        (llPTPullback period hPeriod fields)
        { measureDirection := throatPTPullback period hPeriod Real dMeasure,
          fieldDirection := differentialLLFluxDirectionPT period hPeriod dField }
        { measureDirection := 0,
          fieldDirection := differentialLLFluxDirectionPT period hPeriod testField }
        point =
      llWorldvolumeHessianDensity period hPeriod fields
        { measureDirection := dMeasure, fieldDirection := dField }
        { measureDirection := 0, fieldDirection := testField }
        (fixedThroatPT period hPeriod point) := by
  simp [llWorldvolumeHessianDensity, llPTPullback,
    differentialLLFluxDirectionPT, throatPTPullback]

private theorem integral_ptAverage_eq
    (f : EffectiveThroat period hPeriod → Real)
    (hf : Integrable f (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    (∫ point, ptAverage period hPeriod f point
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, f point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let hPT := intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
    period hPeriod
  have hPTIntegrable : Integrable (f ∘ fixedThroatPT period hPeriod) mu :=
    hPT.integrable_comp_of_integrable hf
  have hPTIntegral := hPT.integral_comp' f
  change (∫ point, f (fixedThroatPT period hPeriod point) ∂mu) =
    ∫ point, f point ∂mu at hPTIntegral
  unfold ptAverage
  rw [integral_const_mul]
  change (1 / 2 : Real) *
      (∫ point, f point + (f ∘ fixedThroatPT period hPeriod) point ∂mu) = _
  rw [integral_add hf hPTIntegrable]
  change (1 / 2 : Real) *
      ((∫ point, f point ∂mu) +
        ∫ point, f (fixedThroatPT period hPeriod point) ∂mu) = _
  rw [hPTIntegral]
  ring

/-- The worldvolume block of a pure field test is exactly the average of its
two raw PT orbits under the canonical throat measure. -/
theorem worldvolume_field_row_pt_orbit_integral
    (fields : IndependentFields period hPeriod)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField testField : SmoothThroatField period hPeriod LLFieldFiber) :
    globalPTLLWorldvolumeHessian period hPeriod fields
        { measureDirection := dMeasure, fieldDirection := dField }
        { measureDirection := 0, fieldDirection := testField }
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      (1 / 2 : Real) *
        ((∫ point,
          llWorldvolumeHessianDensity period hPeriod fields
            { measureDirection := dMeasure, fieldDirection := dField }
            { measureDirection := 0, fieldDirection := testField } point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
         (∫ point,
          llWorldvolumeHessianDensity period hPeriod
            (llPTPullback period hPeriod fields)
            { measureDirection := throatPTPullback period hPeriod Real dMeasure,
              fieldDirection := differentialLLFluxDirectionPT period hPeriod dField }
            { measureDirection := 0,
              fieldDirection := differentialLLFluxDirectionPT period hPeriod testField }
            point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod))) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let raw := llWorldvolumeHessianDensity period hPeriod fields
    { measureDirection := dMeasure, fieldDirection := dField }
    { measureDirection := 0, fieldDirection := testField }
  have hRaw : Integrable raw mu := by
    apply Continuous.integrable_of_hasCompactSupport _
      (HasCompactSupport.of_compactSpace _)
    have hFirst : Continuous (fun point : EffectiveThroat period hPeriod =>
        2 * dMeasure point * inner Real (fields.llField point)
          (testField point)) :=
      ((continuous_const.mul dMeasure.contMDiff_toFun.continuous).mul
        (fields.llField.contMDiff_toFun.continuous.inner
          testField.contMDiff_toFun.continuous))
    have hSecond : Continuous (fun point : EffectiveThroat period hPeriod =>
        2 * fields.llMeasure point * inner Real (dField point)
          (testField point)) :=
      ((continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
        (dField.contMDiff_toFun.continuous.inner
          testField.contMDiff_toFun.continuous))
    have hRawEq : raw = fun point =>
        2 * dMeasure point * inner Real (fields.llField point)
          (testField point) +
        2 * fields.llMeasure point * inner Real (dField point)
          (testField point) := by
      funext point
      simp [raw, llWorldvolumeHessianDensity]
    rw [hRawEq]
    exact hFirst.add hSecond
  have hPTRaw :
      (∫ point,
          llWorldvolumeHessianDensity period hPeriod
            (llPTPullback period hPeriod fields)
            { measureDirection := throatPTPullback period hPeriod Real dMeasure,
              fieldDirection := differentialLLFluxDirectionPT period hPeriod dField }
            { measureDirection := 0,
              fieldDirection := differentialLLFluxDirectionPT period hPeriod testField }
            point ∂mu) =
        ∫ point, raw point ∂mu := by
    rw [show (fun point =>
        llWorldvolumeHessianDensity period hPeriod
          (llPTPullback period hPeriod fields)
          { measureDirection := throatPTPullback period hPeriod Real dMeasure,
            fieldDirection := differentialLLFluxDirectionPT period hPeriod dField }
          { measureDirection := 0,
            fieldDirection := differentialLLFluxDirectionPT period hPeriod testField }
          point) = raw ∘ fixedThroatPT period hPeriod from by
            funext point
            exact raw_worldvolume_pt_point period hPeriod fields dMeasure
              dField testField point]
    exact (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
      period hPeriod).integral_comp' raw
  change (∫ point, ptAverage period hPeriod raw point ∂mu) = _
  rw [integral_ptAverage_eq period hPeriod raw hRaw, hPTRaw]
  ring

end
end P0EFTJanusProgramPT12LLFullFieldJacobiSameActionPairing4D
end JanusFormal

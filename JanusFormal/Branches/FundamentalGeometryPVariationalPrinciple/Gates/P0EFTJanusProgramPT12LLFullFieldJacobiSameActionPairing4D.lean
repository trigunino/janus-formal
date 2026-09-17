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
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
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

/-- The kinetic block is the literal average of the two raw Hessian orbits. -/
theorem kinetic_field_row_pt_orbit_integral
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField testField : SmoothThroatField period hPeriod LLFieldFiber) :
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame
        fields.llAuxMetric fields.llField dAux 0 dField testField
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      (1 / 2 : Real) *
        ((∫ point,
          differentialLLKineticMixedHessianDensity period hPeriod frame
            fields.llAuxMetric fields.llField dAux 0 dField testField point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
         (∫ point,
          differentialLLKineticMixedHessianDensity period hPeriod frame
            (llPTPullback period hPeriod fields).llAuxMetric
            (llPTPullback period hPeriod fields).llField
            (differentialLLAuxMetricDirectionPT period hPeriod dAux) 0
            (differentialLLFluxDirectionPT period hPeriod dField)
            (differentialLLFluxDirectionPT period hPeriod testField) point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod))) := by
  have hRaw := differentialLLKineticMixedHessianDensity_integrable
    period hPeriod frame fields.llAuxMetric fields.llField dAux 0
    dField testField (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hPT := differentialLLKineticMixedHessianDensity_integrable
    period hPeriod frame
    (llPTPullback period hPeriod fields).llAuxMetric
    (llPTPullback period hPeriod fields).llField
    (differentialLLAuxMetricDirectionPT period hPeriod dAux) 0
    (differentialLLFluxDirectionPT period hPeriod dField)
    (differentialLLFluxDirectionPT period hPeriod testField)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hZero : differentialLLAuxMetricDirectionPT period hPeriod
      (0 : SmoothThroatField period hPeriod LLMetricFiber) = 0 := by
    apply SmoothThroatField.ext period hPeriod LLMetricFiber
    intro point
    rfl
  unfold globalPTDifferentialLLKineticMixedHessian
    ptSymmetricDifferentialLLKineticMixedHessianDensity
  rw [integral_const_mul]
  rw [integral_add hRaw (by simpa only [llPTPullback, hZero] using hPT)]
  simp only [llPTPullback, hZero]

/-- The full three-slot weak field row is the PT average of the two proved
raw finite-difference identities. -/
theorem full_field_row_pt_weak_identity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField testField : SmoothThroatField period hPeriod LLFieldFiber) :
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame
        fields.llAuxMetric fields.llField dAux 0 dField testField
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
      globalPTLLWorldvolumeHessian period hPeriod fields
        { measureDirection := dMeasure, fieldDirection := dField }
        { measureDirection := 0, fieldDirection := testField }
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
          dField testField
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
        (1 / 2 : Real) *
          (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
              (auxPlusFields period hPeriod fields dAux) testField
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) -
            globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
              (auxMinusFields period hPeriod fields dAux) testField
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
            (measurePlusFields period hPeriod fields dMeasure) testField
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) -
          globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
            fields testField
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
  have hRaw := raw_field_row_integral period hPeriod frame fields dAux
    dMeasure dField testField
  have hPT := raw_field_row_integral period hPeriod frame
    (llPTPullback period hPeriod fields)
    (differentialLLAuxMetricDirectionPT period hPeriod dAux)
    (throatPTPullback period hPeriod Real dMeasure)
    (differentialLLFluxDirectionPT period hPeriod dField)
    (differentialLLFluxDirectionPT period hPeriod testField)
  rw [← pt_pullback_aux_plus period hPeriod fields dAux,
    ← pt_pullback_aux_minus period hPeriod fields dAux,
    ← pt_pullback_measure_plus period hPeriod fields dMeasure] at hPT
  rw [kinetic_field_row_pt_orbit_integral period hPeriod frame fields dAux
      dField testField,
    worldvolume_field_row_pt_orbit_integral period hPeriod fields dMeasure
      dField testField]
  unfold globalPTSymmetricDifferentialLLFluxHessian
    globalPTSymmetricDifferentialLLFluxFirstVariation
  linear_combination (1 / 2 : Real) * hRaw + (1 / 2 : Real) * hPT

/-- The finite-difference strong row represents the complete PT-averaged
weak field row on the smooth core. -/
theorem llFullFieldJacobiResidual_pairing_eq_pt_weak
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField testField : LLWeakTestSpace period hPeriod) :
    (∫ point,
      inner Real (llFullFieldJacobiResidual period hPeriod fields dAux
        dMeasure dField point) (testField point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields
          dField testField
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
        (1 / 2 : Real) *
          (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (auxPlusFields period hPeriod fields dAux) testField
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) -
            globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (auxMinusFields period hPeriod fields dAux) testField
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (measurePlusFields period hPeriod fields dMeasure) testField
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) -
          globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            fields testField
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  let regularity := smoothLLStrongRegularity period hPeriod frame
  let strong := fun f : IndependentFields period hPeriod =>
    ptSymmetricStrongDifferentialLLEulerField period hPeriod frame regularity f
  let pure := llStrongJacobiResidual period hPeriod fields dField
  let plus := strong (auxPlusFields period hPeriod fields dAux)
  let minus := strong (auxMinusFields period hPeriod fields dAux)
  let measurePlus := strong (measurePlusFields period hPeriod fields dMeasure)
  let base := strong fields
  let pair := fun f : SmoothThroatField period hPeriod LLFieldFiber =>
    fun point => inner Real (f point) (testField point)
  have hInt (f : SmoothThroatField period hPeriod LLFieldFiber) :
      Integrable (pair f) mu :=
    (f.contMDiff_toFun.continuous.inner
      testField.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPoint (point : EffectiveThroat period hPeriod) :
      inner Real (llFullFieldJacobiResidual period hPeriod fields dAux
          dMeasure dField point) (testField point) =
        pair pure point + (1 / 2 : Real) *
          (pair plus point - pair minus point) +
          (pair measurePlus point - pair base point) := by
    change inner Real
      (pure point + (1 / 2 : Real) • (plus point - minus point) +
        (measurePlus point - base point)) (testField point) = _
    simp [pair, inner_add_left, inner_sub_left, real_inner_smul_left]
  have hIntegral :
      (∫ point, inner Real (llFullFieldJacobiResidual period hPeriod fields dAux
        dMeasure dField point) (testField point) ∂mu) =
      (∫ point, pair pure point ∂mu) +
        (1 / 2 : Real) *
          ((∫ point, pair plus point ∂mu) -
            (∫ point, pair minus point ∂mu)) +
        ((∫ point, pair measurePlus point ∂mu) -
          (∫ point, pair base point ∂mu)) := by
    calc
      _ = ∫ point, pair pure point + (1 / 2 : Real) *
          (pair plus point - pair minus point) +
          (pair measurePlus point - pair base point) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with point
        exact hPoint point
      _ = _ := by
        have hAux : Integrable (fun point => (1 / 2 : Real) *
            (pair plus point - pair minus point)) mu :=
          ((hInt plus).sub (hInt minus)).const_mul _
        have hLeft : Integrable (fun point => pair pure point +
            (1 / 2 : Real) * (pair plus point - pair minus point)) mu :=
          (hInt pure).add hAux
        calc
          (∫ point, pair pure point + (1 / 2 : Real) *
              (pair plus point - pair minus point) +
              (pair measurePlus point - pair base point) ∂mu) =
              (∫ point, pair pure point + (1 / 2 : Real) *
                (pair plus point - pair minus point) ∂mu) +
              (∫ point, pair measurePlus point - pair base point ∂mu) :=
            integral_add hLeft ((hInt measurePlus).sub (hInt base))
          _ = (∫ point, pair pure point ∂mu) +
                (∫ point, (1 / 2 : Real) *
                  (pair plus point - pair minus point) ∂mu) +
                (∫ point, pair measurePlus point - pair base point ∂mu) := by
            rw [integral_add (hInt pure) hAux]
          _ = _ := by
            rw [integral_const_mul,
              integral_sub (hInt plus) (hInt minus),
              integral_sub (hInt measurePlus) (hInt base)]
  rw [hIntegral]
  have hPure := llStrongJacobiResidual_pairing_eq_hessian period hPeriod
    fields dField testField
  have hPlus := canonicalDivergenceFreeLLFrame_globalIPP period hPeriod
    (auxPlusFields period hPeriod fields dAux) regularity testField
  have hMinus := canonicalDivergenceFreeLLFrame_globalIPP period hPeriod
    (auxMinusFields period hPeriod fields dAux) regularity testField
  have hMeasurePlus := canonicalDivergenceFreeLLFrame_globalIPP period hPeriod
    (measurePlusFields period hPeriod fields dMeasure) regularity testField
  have hBase := canonicalDivergenceFreeLLFrame_globalIPP period hPeriod
    fields regularity testField
  change (∫ point, pair pure point ∂mu) = _ at hPure
  change globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
      (auxPlusFields period hPeriod fields dAux) testField mu =
    ∫ point, pair plus point ∂mu at hPlus
  change globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
      (auxMinusFields period hPeriod fields dAux) testField mu =
    ∫ point, pair minus point ∂mu at hMinus
  change globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
      (measurePlusFields period hPeriod fields dMeasure) testField mu =
    ∫ point, pair measurePlus point ∂mu at hMeasurePlus
  change globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
      fields testField mu = ∫ point, pair base point ∂mu at hBase
  rw [hPure, ← hPlus, ← hMinus, ← hMeasurePlus, ← hBase]

/-- Pure field test inside the faithful three-slot smooth LL core. -/
def pureFieldTest
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (testField : LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod)) :
    GlobalFullLLSmooth period hPeriod analysis :=
  ((0, 0), testField)

/-- The complete strong field row pairs to the unchanged same-action Hessian
against every pure smooth field test. -/
theorem llFullFieldJacobiResidual_pairing_eq_sameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (testField : LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod)) :
    (∫ point,
      inner Real
        (llFullFieldJacobiResidual period hPeriod
          (data.boundary.llFields period hPeriod)
          direction.1.1 direction.1.2 direction.2.toTest point)
        (testField.toTest point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalCandidateAFullLLSameActionHessian period hPeriod data
        direction (pureFieldTest period hPeriod testField) := by
  rw [llFullFieldJacobiResidual_pairing_eq_pt_weak period hPeriod
    (data.boundary.llFields period hPeriod) direction.1.1 direction.1.2
    direction.2.toTest testField.toTest]
  rw [← full_field_row_pt_weak_identity period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod) direction.1.1 direction.1.2
    direction.2.toTest testField.toTest]
  unfold globalCandidateAFullLLSameActionHessian fullLLHessian
    globalPTFullLLHessianForm
  simp [pureFieldTest, fullDirectionLLVariation,
    globalCandidateAFullLLDirection_llAuxMetric,
    globalCandidateAFullLLDirection_llMeasure,
    globalCandidateAFullLLDirection_llField]

/-- The L² equivalence class has the same faithful same-action pairing. -/
theorem llFullFieldJacobiToL2_pairing_eq_sameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (testField : LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod)) :
    (∫ point,
      inner Real
        (llFullFieldJacobiToL2 period hPeriod
          (data.boundary.llFields period hPeriod)
          direction.1.1 direction.1.2 direction.2.toTest point)
        (testField.toTest point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalCandidateAFullLLSameActionHessian period hPeriod data
        direction (pureFieldTest period hPeriod testField) := by
  rw [← llFullFieldJacobiResidual_pairing_eq_sameActionHessian period hPeriod
    data analysis direction testField]
  apply integral_congr_ae
  filter_upwards [llFullFieldJacobiToL2_ae period hPeriod
    (data.boundary.llFields period hPeriod) direction.1.1 direction.1.2
    direction.2.toTest] with point hPoint
  rw [hPoint]

end
end P0EFTJanusProgramPT12LLFullFieldJacobiSameActionPairing4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D

/-!
# The auxiliary-metric and measure rows of the LL Jacobi operator

These are the two algebraic output rows of the unchanged full three-slot LL
Hessian. The field input still enters through its first derivatives.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D

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

/-- The first-order cross coefficient is a smooth scalar field. -/
private def smoothDerivativePairing
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod Real where
  toFun := throatDerivativePairing period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) first second
  contMDiff_toFun := by
    unfold throatDerivativePairing
    apply ContMDiff.sum
    intro index _
    have hFirst := throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) first
    have hSecond := throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) second
    rw [contMDiff_pi_space] at hFirst hSecond
    exact (((innerSL ℝ (E := LLFieldFiber)).contMDiff.comp
      (hFirst index)).clm_apply (hSecond index))

/-- Raw linearization of the auxiliary-metric Euler residual. -/
def rawLLAuxJacobiResidual
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod LLMetricFiber where
  toFun point :=
    throatDerivativeEnergy period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields.llField point •
      dAux point +
    (2 * throatDerivativePairing period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        fields.llField dField point) • fields.llAuxMetric point
  contMDiff_toFun :=
    ((smoothThroatDerivativeEnergy period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) fields.llField
      ).contMDiff_toFun.smul dAux.contMDiff_toFun).add
      ((contMDiff_const.mul
        (smoothDerivativePairing period hPeriod fields.llField dField
          ).contMDiff_toFun).smul fields.llAuxMetric.contMDiff_toFun)

/-- PT average of the genuine auxiliary-metric Jacobi row. -/
def llAuxJacobiResidual
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod LLMetricFiber :=
  (1 / 2 : Real) •
    (rawLLAuxJacobiResidual period hPeriod fields dAux dField +
      throatPTPullback period hPeriod LLMetricFiber
        (rawLLAuxJacobiResidual period hPeriod
          (llPTPullback period hPeriod fields)
          (differentialLLAuxMetricDirectionPT period hPeriod dAux)
          (differentialLLFluxDirectionPT period hPeriod dField)))

/-- The measure row is the variation of `|Phi|²`; its diagonal block vanishes. -/
def llMeasureJacobiResidual
    (fields : IndependentFields period hPeriod)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod Real where
  toFun point := 2 * inner Real (fields.llField point) (dField point)
  contMDiff_toFun :=
    contMDiff_const.mul
      (((innerSL ℝ (E := LLFieldFiber)).contMDiff.comp
        fields.llField.contMDiff_toFun).clm_apply dField.contMDiff_toFun)

theorem rawLLAuxJacobiResidual_pairing
    (fields : IndependentFields period hPeriod)
    (dAux testAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    inner Real (rawLLAuxJacobiResidual period hPeriod fields dAux dField point)
        (testAux point) =
      differentialLLKineticMixedHessianDensity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        fields.llAuxMetric fields.llField dAux testAux dField 0 point := by
  have hZero : throatDerivativePairing period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      dField (0 : SmoothThroatField period hPeriod LLFieldFiber) point = 0 := by
    simp [throatDerivativePairing]
  have hZero' : throatDerivativePairing period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      fields.llField (0 : SmoothThroatField period hPeriod LLFieldFiber) point =
      0 := by simp [throatDerivativePairing]
  change inner Real
      (throatDerivativeEnergy period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields.llField point •
        dAux point +
      (2 * throatDerivativePairing period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          fields.llField dField point) • fields.llAuxMetric point)
      (testAux point) = _
  simp only [differentialLLKineticMixedHessianDensity, inner_add_left,
    real_inner_smul_left, hZero, hZero', mul_zero, zero_add]
  ring

theorem llMeasureJacobiResidual_pairing
    (fields : IndependentFields period hPeriod)
    (dMeasure testMeasure : SmoothThroatField period hPeriod Real)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    inner Real (llMeasureJacobiResidual period hPeriod fields dField point)
        (testMeasure point) =
      llWorldvolumeHessianDensity period hPeriod fields
        { measureDirection := dMeasure, fieldDirection := dField }
        { measureDirection := testMeasure, fieldDirection := 0 } point := by
  simp [llMeasureJacobiResidual, llWorldvolumeHessianDensity]
  ring

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

/-- The metric output row is the kinetic Hessian against a pure metric test. -/
theorem llAuxJacobiResidual_pairing_eq_kineticHessian
    (fields : IndependentFields period hPeriod)
    (dAux testAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    (∫ point,
      inner Real (llAuxJacobiResidual period hPeriod fields dAux dField point)
        (testAux point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalPTDifferentialLLKineticMixedHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        fields.llAuxMetric fields.llField dAux testAux dField 0
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  let raw := rawLLAuxJacobiResidual period hPeriod fields dAux dField
  let ptRaw := rawLLAuxJacobiResidual period hPeriod
    (llPTPullback period hPeriod fields)
    (differentialLLAuxMetricDirectionPT period hPeriod dAux)
    (differentialLLFluxDirectionPT period hPeriod dField)
  let pulledPtRaw := throatPTPullback period hPeriod LLMetricFiber ptRaw
  have hRawPoint (point) :
      differentialLLKineticMixedHessianDensity period hPeriod frame
          fields.llAuxMetric fields.llField dAux testAux dField 0 point =
        inner Real (raw point) (testAux point) :=
    (rawLLAuxJacobiResidual_pairing period hPeriod fields dAux testAux
      dField point).symm
  have hPtPoint (point) :
      differentialLLKineticMixedHessianDensity period hPeriod frame
          (throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric)
          (throatPTPullback period hPeriod LLFieldFiber fields.llField)
          (differentialLLAuxMetricDirectionPT period hPeriod dAux)
          (differentialLLAuxMetricDirectionPT period hPeriod testAux)
          (differentialLLFluxDirectionPT period hPeriod dField) 0 point =
        inner Real (ptRaw point)
          (differentialLLAuxMetricDirectionPT period hPeriod testAux point) := by
    simpa only [frame, ptRaw, llPTPullback] using
      (rawLLAuxJacobiResidual_pairing period hPeriod
        (llPTPullback period hPeriod fields)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux)
        (differentialLLAuxMetricDirectionPT period hPeriod testAux)
        (differentialLLFluxDirectionPT period hPeriod dField) point).symm
  have hRawIntegrable : Integrable
      (fun point => inner Real (raw point) (testAux point)) mu :=
    (raw.contMDiff_toFun.continuous.inner
      testAux.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPtIntegrable : Integrable
      (fun point => inner Real (ptRaw point)
        (differentialLLAuxMetricDirectionPT period hPeriod testAux point)) mu :=
    (ptRaw.contMDiff_toFun.continuous.inner
      (differentialLLAuxMetricDirectionPT period hPeriod testAux
        ).contMDiff_toFun.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hPulledIntegrable : Integrable
      (fun point => inner Real (pulledPtRaw point) (testAux point)) mu :=
    (pulledPtRaw.contMDiff_toFun.continuous.inner
      testAux.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRawDensityIntegrable : Integrable
      (differentialLLKineticMixedHessianDensity period hPeriod frame
        fields.llAuxMetric fields.llField dAux testAux dField 0) mu :=
    hRawIntegrable.congr (Filter.Eventually.of_forall fun point =>
      (hRawPoint point).symm)
  have hPtDensityIntegrable : Integrable
      (differentialLLKineticMixedHessianDensity period hPeriod frame
        (throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric)
        (throatPTPullback period hPeriod LLFieldFiber fields.llField)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux)
        (differentialLLAuxMetricDirectionPT period hPeriod testAux)
        (differentialLLFluxDirectionPT period hPeriod dField) 0) mu :=
    hPtIntegrable.congr (Filter.Eventually.of_forall fun point =>
      (hPtPoint point).symm)
  have hChangeVariable :
      (∫ point, inner Real (ptRaw point)
          (differentialLLAuxMetricDirectionPT period hPeriod testAux point) ∂mu) =
        ∫ point, inner Real (pulledPtRaw point) (testAux point) ∂mu := by
    have hMap :=
      (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
        period hPeriod).integral_comp'
        (fun point => inner Real (ptRaw point)
          (differentialLLAuxMetricDirectionPT period hPeriod testAux point))
    calc
      _ = ∫ point, inner Real (ptRaw (fixedThroatPT period hPeriod point))
          (differentialLLAuxMetricDirectionPT period hPeriod testAux
            (fixedThroatPT period hPeriod point)) ∂mu := hMap.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with point
        change inner Real (ptRaw (fixedThroatPT period hPeriod point))
            (testAux (fixedThroatPT period hPeriod
              (fixedThroatPT period hPeriod point))) = _
        rw [fixedThroatPT_involutive]
        rfl
  have hZero : differentialLLFluxDirectionPT period hPeriod
      (0 : SmoothThroatField period hPeriod LLFieldFiber) = 0 := by
    apply SmoothThroatField.ext
    intro point
    rfl
  calc
    (∫ point, inner Real
        (llAuxJacobiResidual period hPeriod fields dAux dField point)
        (testAux point) ∂mu) =
      (1 / 2 : Real) *
        ((∫ point, inner Real (raw point) (testAux point) ∂mu) +
          ∫ point, inner Real (pulledPtRaw point) (testAux point) ∂mu) := by
      rw [← integral_add hRawIntegrable hPulledIntegrable,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with point
      change inner Real
          ((1 / 2 : Real) • (raw point + pulledPtRaw point))
          (testAux point) = _
      simp [inner_add_left, real_inner_smul_left]
      ring
    _ = (1 / 2 : Real) *
        ((∫ point, inner Real (raw point) (testAux point) ∂mu) +
          ∫ point, inner Real (ptRaw point)
            (differentialLLAuxMetricDirectionPT period hPeriod testAux point)
            ∂mu) := by rw [hChangeVariable]
    _ = globalPTDifferentialLLKineticMixedHessian period hPeriod frame
          fields.llAuxMetric fields.llField dAux testAux dField 0 mu := by
      unfold globalPTDifferentialLLKineticMixedHessian
        ptSymmetricDifferentialLLKineticMixedHessianDensity
      rw [hZero, integral_const_mul]
      rw [integral_add hRawDensityIntegrable hPtDensityIntegrable]
      congr 1
      congr 1 <;> apply integral_congr_ae <;>
        filter_upwards [] with point
      · exact (hRawPoint point).symm
      · exact (hPtPoint point).symm

/-- The measure output row is the worldvolume Hessian against a pure
measure test. -/
theorem llMeasureJacobiResidual_pairing_eq_worldvolumeHessian
    (fields : IndependentFields period hPeriod)
    (dMeasure testMeasure : SmoothThroatField period hPeriod Real)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    (∫ point,
      inner Real (llMeasureJacobiResidual period hPeriod fields dField point)
        (testMeasure point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalPTLLWorldvolumeHessian period hPeriod fields
        { measureDirection := dMeasure, fieldDirection := dField }
        { measureDirection := testMeasure, fieldDirection := 0 }
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let raw := llWorldvolumeHessianDensity period hPeriod fields
    { measureDirection := dMeasure, fieldDirection := dField }
    { measureDirection := testMeasure, fieldDirection := 0 }
  have hRaw : Integrable raw mu := by
    have hPairing : Integrable
        (fun point => inner Real
          (llMeasureJacobiResidual period hPeriod fields dField point)
          (testMeasure point)) mu :=
      ((llMeasureJacobiResidual period hPeriod fields dField
        ).contMDiff_toFun.continuous.inner
        testMeasure.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    exact hPairing.congr (Filter.Eventually.of_forall fun point =>
      (llMeasureJacobiResidual_pairing period hPeriod fields dMeasure
        testMeasure dField point))
  unfold globalPTLLWorldvolumeHessian ptLLWorldvolumeHessianDensity
  rw [integral_ptAverage_eq period hPeriod raw hRaw]
  apply integral_congr_ae
  filter_upwards [] with point
  exact llMeasureJacobiResidual_pairing period hPeriod fields dMeasure
    testMeasure dField point

/-- Pure auxiliary-metric/measure test inside the faithful three-slot core. -/
def pureAuxMeasureTest
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (testAux : SmoothThroatField period hPeriod LLMetricFiber)
    (testMeasure : SmoothThroatField period hPeriod Real) :
    GlobalFullLLSmooth period hPeriod analysis :=
  ((testAux, testMeasure), 0)

/-- Both L² rows pair to the unchanged full three-slot same-action Hessian. -/
theorem llAuxMeasureJacobiResidual_pairing_eq_sameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (testAux : SmoothThroatField period hPeriod LLMetricFiber)
    (testMeasure : SmoothThroatField period hPeriod Real) :
    (∫ point,
      inner Real
        (llAuxJacobiResidual period hPeriod
          (data.boundary.llFields period hPeriod)
          direction.1.1 direction.2.toTest point)
        (testAux point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
    (∫ point,
      inner Real
        (llMeasureJacobiResidual period hPeriod
          (data.boundary.llFields period hPeriod) direction.2.toTest point)
        (testMeasure point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalCandidateAFullLLSameActionHessian period hPeriod data
        direction (pureAuxMeasureTest period hPeriod testAux testMeasure) := by
  rw [llAuxJacobiResidual_pairing_eq_kineticHessian period hPeriod
      (data.boundary.llFields period hPeriod) direction.1.1 testAux
      direction.2.toTest,
    llMeasureJacobiResidual_pairing_eq_worldvolumeHessian period hPeriod
      (data.boundary.llFields period hPeriod) direction.1.2 testMeasure
      direction.2.toTest]
  unfold globalCandidateAFullLLSameActionHessian fullLLHessian
    globalPTFullLLHessianForm
  simp [pureAuxMeasureTest, fullDirectionLLVariation,
    globalCandidateAFullLLDirection_llAuxMetric,
    globalCandidateAFullLLDirection_llMeasure,
    globalCandidateAFullLLDirection_llField]

/-- Both smooth output rows have actual L² values. -/
def llAuxJacobiToL2
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    Lp LLMetricFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ((llAuxJacobiResidual period hPeriod fields dAux dField).contMDiff_toFun.continuous
    |>.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp
      (llAuxJacobiResidual period hPeriod fields dAux dField)

def llMeasureJacobiToL2
    (fields : IndependentFields period hPeriod)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ((llMeasureJacobiResidual period hPeriod fields dField).contMDiff_toFun.continuous
    |>.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp
      (llMeasureJacobiResidual period hPeriod fields dField)

/-- The pure tests in the two genuine L² target spaces. -/
def llAuxTestToL2
    (test : SmoothThroatField period hPeriod LLMetricFiber) :
    Lp LLMetricFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (test.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).toLp test

def llMeasureTestToL2
    (test : SmoothThroatField period hPeriod Real) :
    Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (test.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).toLp test

private theorem llAuxJacobiToL2_ae
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    (llAuxJacobiToL2 period hPeriod fields dAux dField :
      EffectiveThroat period hPeriod → LLMetricFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      llAuxJacobiResidual period hPeriod fields dAux dField :=
  ((llAuxJacobiResidual period hPeriod fields dAux dField).contMDiff_toFun.continuous
    |>.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).coeFn_toLp

private theorem llMeasureJacobiToL2_ae
    (fields : IndependentFields period hPeriod)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    (llMeasureJacobiToL2 period hPeriod fields dField :
      EffectiveThroat period hPeriod → Real) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      llMeasureJacobiResidual period hPeriod fields dField :=
  ((llMeasureJacobiResidual period hPeriod fields dField).contMDiff_toFun.continuous
    |>.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).coeFn_toLp

private theorem llAuxTestToL2_ae
    (test : SmoothThroatField period hPeriod LLMetricFiber) :
    (llAuxTestToL2 period hPeriod test :
      EffectiveThroat period hPeriod → LLMetricFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod] test :=
  (test.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).coeFn_toLp

private theorem llMeasureTestToL2_ae
    (test : SmoothThroatField period hPeriod Real) :
    (llMeasureTestToL2 period hPeriod test :
      EffectiveThroat period hPeriod → Real) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod] test :=
  (test.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).coeFn_toLp

/-- The two actual L² residual classes represent the full same-action
Hessian on every pure smooth auxiliary-metric/measure test. -/
theorem llAuxMeasureJacobiToL2_pairing_eq_sameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (testAux : SmoothThroatField period hPeriod LLMetricFiber)
    (testMeasure : SmoothThroatField period hPeriod Real) :
    inner Real
        (llAuxJacobiToL2 period hPeriod
          (data.boundary.llFields period hPeriod)
          direction.1.1 direction.2.toTest)
        (llAuxTestToL2 period hPeriod testAux) +
      inner Real
        (llMeasureJacobiToL2 period hPeriod
          (data.boundary.llFields period hPeriod) direction.2.toTest)
        (llMeasureTestToL2 period hPeriod testMeasure) =
      globalCandidateAFullLLSameActionHessian period hPeriod data
        direction (pureAuxMeasureTest period hPeriod testAux testMeasure) := by
  have hAux :
      inner Real
          (llAuxJacobiToL2 period hPeriod
            (data.boundary.llFields period hPeriod)
            direction.1.1 direction.2.toTest)
          (llAuxTestToL2 period hPeriod testAux) =
        ∫ point,
          inner Real
            (llAuxJacobiResidual period hPeriod
              (data.boundary.llFields period hPeriod)
              direction.1.1 direction.2.toTest point)
            (testAux point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards
      [llAuxJacobiToL2_ae period hPeriod
        (data.boundary.llFields period hPeriod)
        direction.1.1 direction.2.toTest,
       llAuxTestToL2_ae period hPeriod testAux]
      with point hResidual hTest
    rw [hResidual, hTest]
  have hMeasure :
      inner Real
          (llMeasureJacobiToL2 period hPeriod
            (data.boundary.llFields period hPeriod) direction.2.toTest)
          (llMeasureTestToL2 period hPeriod testMeasure) =
        ∫ point,
          inner Real
            (llMeasureJacobiResidual period hPeriod
              (data.boundary.llFields period hPeriod) direction.2.toTest point)
            (testMeasure point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards
      [llMeasureJacobiToL2_ae period hPeriod
        (data.boundary.llFields period hPeriod) direction.2.toTest,
       llMeasureTestToL2_ae period hPeriod testMeasure]
      with point hResidual hTest
    rw [hResidual, hTest]
  rw [hAux, hMeasure]
  exact llAuxMeasureJacobiResidual_pairing_eq_sameActionHessian period hPeriod
    data analysis direction testAux testMeasure

end
end P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D
end JanusFormal

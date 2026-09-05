import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLTotalEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLFirstVariationZero4D

/-! # Total auxiliary-metric and measure LL Euler equations -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
open P0EFTJanusTruePTFullLLFirstVariationBridge4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLTotalEuler4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

local instance canonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatMeasureIsOpenPos :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- The derivative energy is a genuine smooth scalar field. -/
def smoothThroatDerivativeEnergy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field : SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod Real where
  toFun := throatDerivativeEnergy period hPeriod frame field
  contMDiff_toFun := by
    unfold throatDerivativeEnergy
    apply ContMDiff.sum
    intro index _
    have hDerivative :=
      throatFrameDerivative_contMDiff period hPeriod LLFieldFiber frame field
    rw [contMDiff_pi_space] at hDerivative
    exact (contDiff_norm_sq Real).contMDiff.comp (hDerivative index)

@[simp]
theorem smoothThroatDerivativeEnergy_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatDerivativeEnergy period hPeriod frame field point =
      throatDerivativeEnergy period hPeriod frame field point :=
  rfl

/-- Raw auxiliary-metric Euler residual `|DΦ|² a`. -/
def rawLLAuxMetricStrongResidual
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod LLMetricFiber where
  toFun point :=
    smoothThroatDerivativeEnergy period hPeriod frame fields.llField point •
      fields.llAuxMetric point
  contMDiff_toFun :=
    (smoothThroatDerivativeEnergy period hPeriod frame fields.llField
      ).contMDiff_toFun.smul fields.llAuxMetric.contMDiff_toFun

@[simp]
theorem rawLLAuxMetricStrongResidual_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    rawLLAuxMetricStrongResidual period hPeriod frame fields point =
      throatDerivativeEnergy period hPeriod frame fields.llField point •
        fields.llAuxMetric point :=
  rfl

/-- PT-averaged pointwise auxiliary-metric Euler residual. -/
def ptSymmetricLLAuxMetricStrongResidual
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod LLMetricFiber :=
  (1 / 2 : Real) •
    (rawLLAuxMetricStrongResidual period hPeriod frame fields +
      throatPTPullback period hPeriod LLMetricFiber
        (rawLLAuxMetricStrongResidual period hPeriod frame
          (llPTPullback period hPeriod fields)))

theorem ptSymmetricLLAuxMetricStrongResidual_apply_raw
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricLLAuxMetricStrongResidual period hPeriod frame fields point =
      (1 / 2 : Real) •
        (rawLLAuxMetricStrongResidual period hPeriod frame fields point +
          rawLLAuxMetricStrongResidual period hPeriod frame
            (llPTPullback period hPeriod fields)
              (fixedThroatPT period hPeriod point)) :=
  rfl

@[simp]
theorem ptSymmetricLLAuxMetricStrongResidual_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricLLAuxMetricStrongResidual period hPeriod frame fields point =
      (1 / 2 : Real) •
        (throatDerivativeEnergy period hPeriod frame fields.llField point •
            fields.llAuxMetric point +
          throatDerivativeEnergy period hPeriod frame
              (llPTPullback period hPeriod fields).llField
              (fixedThroatPT period hPeriod point) •
            fields.llAuxMetric point) := by
  rw [ptSymmetricLLAuxMetricStrongResidual_apply_raw]
  simp only [rawLLAuxMetricStrongResidual_apply]
  simp [llPTPullback, throatPTPullback_apply, fixedThroatPT_involutive]

/-- Algebraic Euler residual of the independent LL measure. -/
def llMeasureStrongResidual
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod Real where
  toFun point := ‖fields.llField point‖ ^ 2
  contMDiff_toFun :=
    (contDiff_norm_sq Real).contMDiff.comp fields.llField.contMDiff_toFun

@[simp]
theorem llMeasureStrongResidual_apply
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    llMeasureStrongResidual period hPeriod fields point =
      ‖fields.llField point‖ ^ 2 :=
  rfl

/-- Smooth tests separate any finite-dimensional Hilbert-valued residual. -/
theorem smoothThroatField_pairing_detects_pointwise_zero
    {Fiber : Type*} [NormedAddCommGroup Fiber] [InnerProductSpace Real Fiber]
    (residual : SmoothThroatField period hPeriod Fiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    [mu.IsOpenPosMeasure] :
    (∀ direction : SmoothThroatField period hPeriod Fiber,
        (∫ point, inner Real (residual point) (direction point) ∂mu) = 0) ↔
      ∀ point : EffectiveThroat period hPeriod, residual point = 0 := by
  constructor
  · intro hPairing
    have hSelf := hPairing residual
    have hSquareIntegral :
        (∫ point, ‖residual point‖ ^ 2 ∂mu) = 0 := by
      simpa only [real_inner_self_eq_norm_sq] using hSelf
    have hSquareIntegrable :
        Integrable (fun point => ‖residual point‖ ^ 2) mu :=
      (residual.contMDiff_toFun.continuous.norm.pow 2
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hSquareZero :
        (fun point => ‖residual point‖ ^ 2) =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun point => sq_nonneg ‖residual point‖)
        hSquareIntegrable).mp hSquareIntegral
    have hResidualZero :
        residual.toFun =ᵐ[mu]
          (fun _ : EffectiveThroat period hPeriod => (0 : Fiber)) := by
      filter_upwards [hSquareZero] with point hPoint
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hPoint)
    have hFunctionZero :
        residual.toFun =
          (fun _ : EffectiveThroat period hPeriod => (0 : Fiber)) :=
      (Continuous.ae_eq_iff_eq mu residual.contMDiff_toFun.continuous
        continuous_const).mp hResidualZero
    exact fun point => congrFun hFunctionZero point
  · intro hPointwise direction
    apply integral_eq_zero_of_ae
    filter_upwards [] with point
    rw [hPointwise point]
    simp

/-- Pure auxiliary-metric LL test. -/
abbrev RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricTest :=
  SmoothThroatField period hPeriod LLMetricFiber

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricThreeSlotTest
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricTest
      period hPeriod) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod :=
  (test, (0, 0))

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricTest
      period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period hPeriod
    configuration
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricThreeSlotTest
        period hPeriod test)

/-- Pure independent-measure LL test. -/
abbrev RegularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureTest :=
  SmoothThroatField period hPeriod Real

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureThreeSlotTest
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureTest
      period hPeriod) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod :=
  (0, (test, 0))

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureTest
      period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period hPeriod
    configuration
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureThreeSlotTest
        period hPeriod test)

theorem globalPTKineticFirstVariation_pureAux_eq_residualPairing
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod LLMetricFiber) :
    (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
        fields.llAuxMetric fields.llField test 0 point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, inner Real
        (ptSymmetricLLAuxMetricStrongResidual period hPeriod frame fields point)
        (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let raw := rawLLAuxMetricStrongResidual period hPeriod frame fields
  let ptRaw := rawLLAuxMetricStrongResidual period hPeriod frame
    (llPTPullback period hPeriod fields)
  let pulledPtRaw := throatPTPullback period hPeriod LLMetricFiber ptRaw
  have hRawPoint : ∀ point,
      differentialLLKineticFirstVariation period hPeriod frame
          fields.llAuxMetric fields.llField test 0 point =
        inner Real (raw point) (test point) := by
    intro point
    simp [differentialLLKineticFirstVariation, throatDerivativePairing,
      raw, rawLLAuxMetricStrongResidual, real_inner_smul_left, mul_comm]
  have hPtRawPoint : ∀ point,
      differentialLLKineticFirstVariation period hPeriod frame
          (throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric)
          (throatPTPullback period hPeriod LLFieldFiber fields.llField)
          (differentialLLAuxMetricDirectionPT period hPeriod test) 0 point =
        inner Real (ptRaw point)
          (differentialLLAuxMetricDirectionPT period hPeriod test point) := by
    intro point
    simp [differentialLLKineticFirstVariation, throatDerivativePairing,
      ptRaw, rawLLAuxMetricStrongResidual, llPTPullback,
      real_inner_smul_left, mul_comm]
  have hChangeVariable :
      (∫ point, inner Real (ptRaw point)
          (differentialLLAuxMetricDirectionPT period hPeriod test point) ∂mu) =
        ∫ point, inner Real (pulledPtRaw point) (test point) ∂mu := by
    have hMap :=
      (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
        period hPeriod).integral_comp'
        (fun point => inner Real (ptRaw point)
          (differentialLLAuxMetricDirectionPT period hPeriod test point))
    calc
      (∫ point, inner Real (ptRaw point)
          (differentialLLAuxMetricDirectionPT period hPeriod test point) ∂mu) =
          ∫ point, inner Real
            (ptRaw (fixedThroatPT period hPeriod point))
            (differentialLLAuxMetricDirectionPT period hPeriod test
              (fixedThroatPT period hPeriod point)) ∂mu := hMap.symm
      _ = ∫ point, inner Real (pulledPtRaw point) (test point) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with point
        change inner Real
            (ptRaw (fixedThroatPT period hPeriod point))
            (test (fixedThroatPT period hPeriod
              (fixedThroatPT period hPeriod point))) = _
        rw [fixedThroatPT_involutive]
        rfl
  have hRawIntegrable : Integrable
      (fun point => inner Real (raw point) (test point)) mu :=
    (raw.contMDiff_toFun.continuous.inner
      test.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPtRawIntegrable : Integrable
      (fun point => inner Real (ptRaw point)
        (differentialLLAuxMetricDirectionPT period hPeriod test point)) mu :=
    (ptRaw.contMDiff_toFun.continuous.inner
      (differentialLLAuxMetricDirectionPT period hPeriod test
        ).contMDiff_toFun.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hPulledIntegrable : Integrable
      (fun point => inner Real (pulledPtRaw point) (test point)) mu :=
    (pulledPtRaw.contMDiff_toFun.continuous.inner
      test.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRawVariationIntegrable : Integrable
      (differentialLLKineticFirstVariation period hPeriod frame
        fields.llAuxMetric fields.llField test 0) mu := by
    apply hRawIntegrable.congr
    exact Filter.Eventually.of_forall (fun point => (hRawPoint point).symm)
  have hPtRawVariationIntegrable : Integrable
      (differentialLLKineticFirstVariation period hPeriod frame
        (throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric)
        (throatPTPullback period hPeriod LLFieldFiber fields.llField)
        (differentialLLAuxMetricDirectionPT period hPeriod test) 0) mu := by
    apply hPtRawIntegrable.congr
    exact Filter.Eventually.of_forall (fun point => (hPtRawPoint point).symm)
  have hPTZero :
      differentialLLFluxDirectionPT period hPeriod
          (0 : SmoothThroatField period hPeriod LLFieldFiber) = 0 := by
    apply SmoothThroatField.ext period hPeriod LLFieldFiber
    intro point
    rfl
  calc
    (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
        fields.llAuxMetric fields.llField test 0 point ∂mu) =
        (1 / 2 : Real) *
          ((∫ point, inner Real (raw point) (test point) ∂mu) +
            ∫ point, inner Real (ptRaw point)
              (differentialLLAuxMetricDirectionPT period hPeriod test point)
              ∂mu) := by
      unfold ptSymmetricDifferentialLLKineticFirstVariation
      rw [hPTZero, integral_const_mul]
      rw [integral_add hRawVariationIntegrable hPtRawVariationIntegrable]
      · congr 2 <;> apply integral_congr_ae <;>
          filter_upwards [] with point
        · exact hRawPoint point
        · exact hPtRawPoint point
    _ = (1 / 2 : Real) *
          ((∫ point, inner Real (raw point) (test point) ∂mu) +
            ∫ point, inner Real (pulledPtRaw point) (test point) ∂mu) := by
      rw [hChangeVariable]
    _ = ∫ point, inner Real
        (ptSymmetricLLAuxMetricStrongResidual period hPeriod frame fields point)
        (test point) ∂mu := by
      rw [← integral_add hRawIntegrable hPulledIntegrable,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with point
      simp only [ptSymmetricLLAuxMetricStrongResidual_apply_raw,
        inner_add_left, real_inner_smul_left]
      rfl

theorem globalPTLLFirstVariation_pureMeasure_eq_residualPairing
    (fields : IndependentFields period hPeriod)
    (test : SmoothThroatField period hPeriod Real) :
    globalPTLLFirstVariation period hPeriod fields
        { measureDirection := test, fieldDirection := 0 }
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      ∫ point, inner Real
        (llMeasureStrongResidual period hPeriod fields point) (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let variation : LLVariation period hPeriod :=
    { measureDirection := test, fieldDirection := 0 }
  have hPTVariation :
      llVariationPT period hPeriod variation =
        llVariationPTPullback period hPeriod variation :=
    rfl
  rw [globalPTLLFirstVariation_eq_orbit_average]
  rw [hPTVariation, globalLLFirstVariation_pt period hPeriod fields variation
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving period hPeriod)]
  change (1 / 2 : Real) *
      (globalLLFirstVariation period hPeriod fields variation
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
       globalLLFirstVariation period hPeriod fields variation
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = _
  ring_nf
  unfold globalLLFirstVariation llFirstVariationDensity variation
  apply integral_congr_ae
  filter_upwards [] with point
  simp [llMeasureStrongResidual, mul_comm]

theorem fullLLEuler_pureStrongLLAuxMetric_eq_residualPairing
    (fields : IndependentFields period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricTest
      period hPeriod) :
    fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        fields
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricThreeSlotTest
            period hPeriod test))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      ∫ throatPoint, inner Real
        (ptSymmetricLLAuxMetricStrongResidual period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields throatPoint)
        (test throatPoint)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  change
    (∫ throatPoint,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        fields.llAuxMetric fields.llField test 0 throatPoint
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
      globalPTLLFirstVariation period hPeriod fields
        (zeroLLVariation period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = _
  rw [globalPTLLFirstVariation_zero, add_zero]
  exact globalPTKineticFirstVariation_pureAux_eq_residualPairing period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) fields test

theorem fullLLEuler_pureStrongLLMeasure_eq_residualPairing
    (fields : IndependentFields period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureTest
      period hPeriod) :
    fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        fields
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureThreeSlotTest
            period hPeriod test))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      ∫ throatPoint, inner Real
        (llMeasureStrongResidual period hPeriod fields throatPoint)
        (test throatPoint)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  change
    (∫ throatPoint,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        fields.llAuxMetric fields.llField 0 0 throatPoint
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
      globalPTLLFirstVariation period hPeriod fields
        { measureDirection := test, fieldDirection := 0 }
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = _
  rw [show (∫ throatPoint,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        fields.llAuxMetric fields.llField 0 0 throatPoint
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = 0 by simp]
  rw [zero_add]
  exact globalPTLLFirstVariation_pureMeasure_eq_residualPairing period hPeriod
    fields test

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (measure : Measure (EffectiveQuotient period hPeriod))
variable [IsFiniteMeasure measure]
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

theorem regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLAuxMetric_eq_pairing
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricTest
      period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricDirection
          period hPeriod configuration.physical test) =
      ∫ throatPoint, inner Real
        (ptSymmetricLLAuxMetricStrongResidual period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
            configuration.physical point) throatPoint)
        (test throatPoint)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricDirection]
  rw [regular_general_metric_c2_paired_minimal_physical_total_strong_LL_weak_variation_gate
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricThreeSlotTest
        period hPeriod test)]
  exact fullLLEuler_pureStrongLLAuxMetric_eq_residualPairing period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration.physical point) test

theorem regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLMeasure_eq_pairing
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureTest
      period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureDirection
          period hPeriod configuration.physical test) =
      ∫ throatPoint, inner Real
        (llMeasureStrongResidual period hPeriod
          (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
            configuration.physical point) throatPoint)
        (test throatPoint)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureDirection]
  rw [regular_general_metric_c2_paired_minimal_physical_total_strong_LL_weak_variation_gate
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureThreeSlotTest
        period hPeriod test)]
  exact fullLLEuler_pureStrongLLMeasure_eq_residualPairing period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration.physical point) test

/-- Gate445a: total stationarity in every auxiliary-metric LL direction is
the explicit PT-averaged pointwise auxiliary equation. -/
theorem regular_general_metric_c2_paired_minimal_physical_total_strong_LL_aux_metric_stationary_iff_strong_equation_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (∀ test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricTest
        period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricDirection
            period hPeriod configuration.physical test) = 0) ↔
      ∀ throatPoint : EffectiveThroat period hPeriod,
        ptSymmetricLLAuxMetricStrongResidual period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
            configuration.physical point) throatPoint = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [← smoothThroatField_pairing_detects_pointwise_zero period hPeriod
    (ptSymmetricLLAuxMetricStrongResidual period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
        configuration.physical point))
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
  constructor
  · intro hTotal test
    rw [← regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLAuxMetric_eq_pairing
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact hTotal test
  · intro hPairing test
    rw [regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLAuxMetric_eq_pairing
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact hPairing test

/-- Gate445b: total stationarity in every independent-measure LL direction is
the explicit algebraic equation `‖Φ‖² = 0`. -/
theorem regular_general_metric_c2_paired_minimal_physical_total_strong_LL_measure_stationary_iff_strong_equation_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (∀ test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureTest
        period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureDirection
            period hPeriod configuration.physical test) = 0) ↔
      ∀ throatPoint : EffectiveThroat period hPeriod,
        ‖(regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point).llField throatPoint‖ ^ 2 = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  change _ ↔ ∀ throatPoint : EffectiveThroat period hPeriod,
    llMeasureStrongResidual period hPeriod
      (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
        configuration.physical point) throatPoint = 0
  rw [← smoothThroatField_pairing_detects_pointwise_zero period hPeriod
    (llMeasureStrongResidual period hPeriod
      (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
        configuration.physical point))
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
  constructor
  · intro hTotal test
    rw [← regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLMeasure_eq_pairing
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact hTotal test
  · intro hPairing test
    rw [regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLMeasure_eq_pairing
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact hPairing test

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
end JanusFormal

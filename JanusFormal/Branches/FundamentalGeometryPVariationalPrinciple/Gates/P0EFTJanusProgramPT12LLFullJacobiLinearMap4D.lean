import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullFieldJacobiSameActionPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D

/-! # Linear L² realization of the complete smooth three-slot LL Jacobi row -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiLinearMap4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D
open P0EFTJanusProgramPT12LLFullFieldJacobiL2Core4D
open P0EFTJanusProgramPT12LLFullFieldJacobiSameActionPairing4D

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

def fullFieldResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  llFullFieldJacobiResidual period hPeriod
    (data.boundary.llFields period hPeriod)
    direction.1.1 direction.1.2 direction.2.toTest

def fullFieldToL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  llFullFieldJacobiToL2 period hPeriod
    (data.boundary.llFields period hPeriod)
    direction.1.1 direction.1.2 direction.2.toTest

private theorem smooth_pairing_injective
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (hPairing : ∀ test : LLWeakTestSpace period hPeriod,
      (∫ point, inner Real (first point) (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, inner Real (second point) (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    first = second := by
  letI : (intrinsicCanonicalThroatVolumeMeasure period hPeriod).IsOpenPosMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  have hZero := (smoothLLField_pairing_detects_pointwise_zero period hPeriod
    (first - second) (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).mp
  have hIntegrable (field test : SmoothThroatField period hPeriod LLFieldFiber) :
      Integrable (fun point => inner Real (field point) (test point))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (field.contMDiff_toFun.continuous.inner test.contMDiff_toFun.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply SmoothThroatField.ext
  intro point
  have hPoint := hZero (by
    intro test
    have hApply (point) : (first - second) point = first point - second point := rfl
    simp only [hApply, inner_sub_left]
    rw [integral_sub (hIntegrable first test) (hIntegrable second test),
      hPairing test, sub_self]) point
  exact sub_eq_zero.mp hPoint

private def toLLFullWeakTangent
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    LLFullWeakTangent period hPeriod :=
  (direction.1.1, (direction.1.2, direction.2.toTest))

private theorem toLLFullWeakTangent_add
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    toLLFullWeakTangent period hPeriod (first + second) =
      toLLFullWeakTangent period hPeriod first +
        toLLFullWeakTangent period hPeriod second :=
  rfl

private theorem toLLFullWeakTangent_smul
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (scalar : Real)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    toLLFullWeakTangent period hPeriod (scalar • direction) =
      scalar • toLLFullWeakTangent period hPeriod direction :=
  rfl

private theorem sameActionHessian_eq_llFullWeakHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLSameActionHessian period hPeriod data first second =
      llFullWeakHessian period hPeriod
        (P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D.canonicalDivergenceFreeLLFrame
          period hPeriod)
        (data.boundary.llFields period hPeriod)
        (toLLFullWeakTangent period hPeriod first)
        (toLLFullWeakTangent period hPeriod second)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  unfold globalCandidateAFullLLSameActionHessian fullLLHessian
    globalPTFullLLHessianForm llFullWeakHessian
    llFullWeakVariation toLLFullWeakTangent fullDirectionLLVariation
  simp [globalCandidateAFullLLDirection_llAuxMetric,
    globalCandidateAFullLLDirection_llMeasure,
    globalCandidateAFullLLDirection_llField]

private theorem sameActionHessian_add_left
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second test : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLSameActionHessian period hPeriod data
        (first + second) test =
      globalCandidateAFullLLSameActionHessian period hPeriod data first test +
      globalCandidateAFullLLSameActionHessian period hPeriod data second test := by
  rw [sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    toLLFullWeakTangent_add]
  exact llFullWeakHessian_add_left period hPeriod
    (P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D.canonicalDivergenceFreeLLFrame
      period hPeriod)
    (data.boundary.llFields period hPeriod)
    (toLLFullWeakTangent period hPeriod first)
    (toLLFullWeakTangent period hPeriod second)
    (toLLFullWeakTangent period hPeriod test)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

private theorem sameActionHessian_smul_left
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (scalar : Real)
    (direction test : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLSameActionHessian period hPeriod data
        (scalar • direction) test =
      scalar * globalCandidateAFullLLSameActionHessian period hPeriod data
        direction test := by
  rw [sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    toLLFullWeakTangent_smul]
  exact llFullWeakHessian_smul_left period hPeriod
    (P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D.canonicalDivergenceFreeLLFrame
      period hPeriod)
    (data.boundary.llFields period hPeriod) scalar
    (toLLFullWeakTangent period hPeriod direction)
    (toLLFullWeakTangent period hPeriod test)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

private theorem sameActionHessian_add_right
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction first second : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLSameActionHessian period hPeriod data
        direction (first + second) =
      globalCandidateAFullLLSameActionHessian period hPeriod data
        direction first +
      globalCandidateAFullLLSameActionHessian period hPeriod data
        direction second := by
  rw [sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    sameActionHessian_eq_llFullWeakHessian period hPeriod data analysis,
    toLLFullWeakTangent_add]
  exact llFullWeakHessian_add_right period hPeriod
    (P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D.canonicalDivergenceFreeLLFrame
      period hPeriod)
    (data.boundary.llFields period hPeriod)
    (toLLFullWeakTangent period hPeriod first)
    (toLLFullWeakTangent period hPeriod second)
    (toLLFullWeakTangent period hPeriod direction)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem fullFieldResidual_add
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    fullFieldResidual period hPeriod data analysis (first + second) =
      fullFieldResidual period hPeriod data analysis first +
        fullFieldResidual period hPeriod data analysis second := by
  apply smooth_pairing_injective period hPeriod
  intro test
  let tagged := LLH1Smooth.ofTest period hPeriod
    (analysis.llH1Data period hPeriod) test
  have hApply (point) :
      (fullFieldResidual period hPeriod data analysis first +
        fullFieldResidual period hPeriod data analysis second) point =
      fullFieldResidual period hPeriod data analysis first point +
        fullFieldResidual period hPeriod data analysis second point := rfl
  simp only [hApply, inner_add_left]
  rw [integral_add]
  · change
      (∫ point, inner Real
        (llFullFieldJacobiResidual period hPeriod
          (data.boundary.llFields period hPeriod)
          (first + second).1.1 (first + second).1.2
          (first + second).2.toTest point) (tagged.toTest point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = _
    rw [llFullFieldJacobiResidual_pairing_eq_sameActionHessian period hPeriod
      data analysis (first + second) tagged]
    change globalCandidateAFullLLSameActionHessian period hPeriod data
        (first + second) (pureFieldTest period hPeriod tagged) =
      (∫ point, inner Real
        (llFullFieldJacobiResidual period hPeriod
          (data.boundary.llFields period hPeriod)
          first.1.1 first.1.2 first.2.toTest point)
        (tagged.toTest point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
      (∫ point, inner Real
        (llFullFieldJacobiResidual period hPeriod
          (data.boundary.llFields period hPeriod)
          second.1.1 second.1.2 second.2.toTest point)
        (tagged.toTest point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    rw [llFullFieldJacobiResidual_pairing_eq_sameActionHessian period hPeriod
        data analysis first tagged,
      llFullFieldJacobiResidual_pairing_eq_sameActionHessian period hPeriod
        data analysis second tagged]
    exact sameActionHessian_add_left period hPeriod data analysis first second
      (pureFieldTest period hPeriod tagged)
  · exact ((fullFieldResidual period hPeriod data analysis first
      ).contMDiff_toFun.continuous.inner test.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((fullFieldResidual period hPeriod data analysis second
      ).contMDiff_toFun.continuous.inner test.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fullFieldResidual_smul
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (scalar : Real)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    fullFieldResidual period hPeriod data analysis (scalar • direction) =
      scalar • fullFieldResidual period hPeriod data analysis direction := by
  apply smooth_pairing_injective period hPeriod
  intro test
  let tagged := LLH1Smooth.ofTest period hPeriod
    (analysis.llH1Data period hPeriod) test
  have hApply (point) :
      (scalar • fullFieldResidual period hPeriod data analysis direction) point =
      scalar • fullFieldResidual period hPeriod data analysis direction point := rfl
  simp only [hApply, real_inner_smul_left, integral_const_mul]
  change
    (∫ point, inner Real
      (llFullFieldJacobiResidual period hPeriod
        (data.boundary.llFields period hPeriod)
        (scalar • direction).1.1 (scalar • direction).1.2
        (scalar • direction).2.toTest point) (tagged.toTest point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = _
  rw [llFullFieldJacobiResidual_pairing_eq_sameActionHessian period hPeriod
    data analysis (scalar • direction) tagged]
  change globalCandidateAFullLLSameActionHessian period hPeriod data
      (scalar • direction) (pureFieldTest period hPeriod tagged) =
    scalar * (∫ point, inner Real
      (llFullFieldJacobiResidual period hPeriod
        (data.boundary.llFields period hPeriod)
        direction.1.1 direction.1.2 direction.2.toTest point)
      (tagged.toTest point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod))
  rw [llFullFieldJacobiResidual_pairing_eq_sameActionHessian period hPeriod
    data analysis direction tagged]
  exact sameActionHessian_smul_left period hPeriod data analysis scalar
    direction (pureFieldTest period hPeriod tagged)

theorem fullFieldToL2_add
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    fullFieldToL2 period hPeriod data analysis (first + second) =
      fullFieldToL2 period hPeriod data analysis first +
        fullFieldToL2 period hPeriod data analysis second := by
  apply Lp.ext
  filter_upwards
    [llFullFieldJacobiToL2_ae period hPeriod
      (data.boundary.llFields period hPeriod) (first + second).1.1
      (first + second).1.2 (first + second).2.toTest,
     llFullFieldJacobiToL2_ae period hPeriod
      (data.boundary.llFields period hPeriod) first.1.1 first.1.2
      first.2.toTest,
     llFullFieldJacobiToL2_ae period hPeriod
      (data.boundary.llFields period hPeriod) second.1.1 second.1.2
      second.2.toTest,
     Lp.coeFn_add (fullFieldToL2 period hPeriod data analysis first)
       (fullFieldToL2 period hPeriod data analysis second)]
    with point hSum hFirst hSecond hAdd
  unfold fullFieldToL2 at hAdd ⊢
  simp only [Pi.add_apply] at hAdd
  rw [hSum, hAdd, hFirst, hSecond]
  exact congrArg (fun field : SmoothThroatField period hPeriod LLFieldFiber =>
    field.toFun point)
    (fullFieldResidual_add period hPeriod data analysis first second)

theorem fullFieldToL2_smul
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (scalar : Real)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    fullFieldToL2 period hPeriod data analysis (scalar • direction) =
      scalar • fullFieldToL2 period hPeriod data analysis direction := by
  apply Lp.ext
  filter_upwards
    [llFullFieldJacobiToL2_ae period hPeriod
      (data.boundary.llFields period hPeriod) (scalar • direction).1.1
      (scalar • direction).1.2 (scalar • direction).2.toTest,
     llFullFieldJacobiToL2_ae period hPeriod
      (data.boundary.llFields period hPeriod) direction.1.1 direction.1.2
      direction.2.toTest,
     Lp.coeFn_smul scalar (fullFieldToL2 period hPeriod data analysis direction)]
    with point hScaled hDirection hSmul
  unfold fullFieldToL2 at hSmul ⊢
  simp only [Pi.smul_apply] at hSmul
  rw [hScaled, hSmul, hDirection]
  exact congrArg (fun field : SmoothThroatField period hPeriod LLFieldFiber =>
    field.toFun point)
    (fullFieldResidual_smul period hPeriod data analysis scalar direction)

/-- The actual field-output row is real-linear on the faithful smooth core. -/
def llFullFieldJacobiLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toFun := fullFieldToL2 period hPeriod data analysis
  map_add' := fullFieldToL2_add period hPeriod data analysis
  map_smul' := fullFieldToL2_smul period hPeriod data analysis

/-- The three genuine L² output rows of the smooth LL Jacobi operator. -/
def llFullJacobiLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      ((Lp LLMetricFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
        Lp Real (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ×
        Lp LLFieldFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) where
  toFun direction :=
    (llAuxMeasureJacobiLinearMap period hPeriod data analysis direction,
      llFullFieldJacobiLinearMap period hPeriod data analysis direction)
  map_add' first second := by
    apply Prod.ext
    · exact (llAuxMeasureJacobiLinearMap period hPeriod data analysis).map_add
        first second
    · exact (llFullFieldJacobiLinearMap period hPeriod data analysis).map_add
        first second
  map_smul' scalar direction := by
    apply Prod.ext
    · exact (llAuxMeasureJacobiLinearMap period hPeriod data analysis).map_smul
        scalar direction
    · exact (llFullFieldJacobiLinearMap period hPeriod data analysis).map_smul
        scalar direction

def llFieldTestToL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (testField : LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod)) :
    Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (testField.toTest.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).toLp testField.toTest

private theorem llFieldTestToL2_ae
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (testField : LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod)) :
    (llFieldTestToL2 period hPeriod testField :
      EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod] testField.toTest :=
  (testField.toTest.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).coeFn_toLp

theorem llFullFieldJacobiLinearMap_pairing_eq_sameActionHessian
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
    inner Real
        (llFullFieldJacobiLinearMap period hPeriod data analysis direction)
        (llFieldTestToL2 period hPeriod testField) =
      globalCandidateAFullLLSameActionHessian period hPeriod data direction
        (pureFieldTest period hPeriod testField) := by
  rw [L2.inner_def]
  have hPairing := llFullFieldJacobiToL2_pairing_eq_sameActionHessian
    period hPeriod data analysis direction testField
  rw [← hPairing]
  apply integral_congr_ae
  filter_upwards [llFieldTestToL2_ae period hPeriod testField]
    with point hTest
  rw [hTest]
  rfl

private theorem smooth_test_decomposition
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (test : GlobalFullLLSmooth period hPeriod analysis) :
    pureAuxMeasureTest period hPeriod test.1.1 test.1.2 +
      pureFieldTest period hPeriod test.2 = test := by
  rcases test with ⟨⟨testAux, testMeasure⟩, testField⟩
  simp [pureAuxMeasureTest, pureFieldTest]

/-- The bundled three-row L² Jacobi map represents the unchanged full LL
same-action Hessian against every smooth three-slot test. -/
theorem llFullJacobiLinearMap_pairing_eq_sameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction test : GlobalFullLLSmooth period hPeriod analysis) :
    inner Real
        ((llFullJacobiLinearMap period hPeriod data analysis direction).1.1)
        (llAuxTestToL2 period hPeriod test.1.1) +
      inner Real
        ((llFullJacobiLinearMap period hPeriod data analysis direction).1.2)
        (llMeasureTestToL2 period hPeriod test.1.2) +
      inner Real
        ((llFullJacobiLinearMap period hPeriod data analysis direction).2)
        (llFieldTestToL2 period hPeriod test.2) =
      globalCandidateAFullLLSameActionHessian period hPeriod data
        direction test := by
  have hAux := llAuxMeasureJacobiLinearMap_pairing_eq_sameActionHessian
    period hPeriod data analysis direction test.1.1 test.1.2
  have hField := llFullFieldJacobiLinearMap_pairing_eq_sameActionHessian
    period hPeriod data analysis direction test.2
  change
    (inner Real
        ((llAuxMeasureJacobiLinearMap period hPeriod data analysis direction).1)
        (llAuxTestToL2 period hPeriod test.1.1) +
      inner Real
        ((llAuxMeasureJacobiLinearMap period hPeriod data analysis direction).2)
        (llMeasureTestToL2 period hPeriod test.1.2)) +
      inner Real
        (llFullFieldJacobiLinearMap period hPeriod data analysis direction)
        (llFieldTestToL2 period hPeriod test.2) = _
  rw [hAux, hField,
    ← sameActionHessian_add_right period hPeriod data analysis direction
      (pureAuxMeasureTest period hPeriod test.1.1 test.1.2)
      (pureFieldTest period hPeriod test.2),
    smooth_test_decomposition period hPeriod test]

end
end P0EFTJanusProgramPT12LLFullJacobiLinearMap4D
end JanusFormal

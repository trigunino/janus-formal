import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

/-!
# On-shell Fredholm reduction of the complete LL graph

At an LL stationary background, the independent measure equation forces the
background LL field to vanish.  The resulting complete three-slot graph
Hessian reduces exactly to its positive LL-field factor.  After quotienting
by the kernel of that projection, its Riesz operator is the identity and is
Fredholm of index zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open Set
open MeasureTheory
open scoped Manifold ContDiff Topology ENNReal InnerProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusThroatLinearOperationsZero4D

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

local instance :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

noncomputable local instance fullLLGraphAmbientInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphAmbient period hPeriod data analysis) := by
  infer_instance

noncomputable local instance fullLLGraphInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  Submodule.innerProductSpace
    (globalCandidateAFullLLGraphSubmodule period hPeriod data analysis)

/-- Pointwise LL stationarity forces the background LL field to vanish. -/
theorem llField_eq_zero_of_stationary
    (fields : IndependentFields period hPeriod)
    (hStationary : ∀ point, LLStationaryAt period hPeriod fields point) :
    fields.llField = 0 := by
  apply SmoothThroatField.ext
  intro point
  change fields.llField point = (0 : LLFieldFiber)
  exact (llStationaryAt_iff_zeroFlux period hPeriod fields point).mp
    (hStationary point)

theorem globalCandidateALLAuxWeight_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (point : EffectiveThroat period hPeriod) :
    globalCandidateALLAuxWeight period hPeriod data point = 0 := by
  unfold globalCandidateALLAuxWeight
  rw [hZero]
  simp [throatDerivativeEnergy]

theorem globalCandidateALLAuxPTWeight_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (point : EffectiveThroat period hPeriod) :
    globalCandidateALLAuxPTWeight period hPeriod data point = 0 := by
  unfold globalCandidateALLAuxPTWeight
  rw [hZero, throatPTPullback_zero]
  simp [throatDerivativeEnergy]

theorem globalCandidateALLAuxMeasureFeatureProjection_smooth_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (direction : GlobalLLAuxMeasureSmooth period hPeriod) :
    globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
        (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
          data direction) = 0 := by
  apply Lp.ext
  filter_upwards
    [globalCandidateALLAuxMeasureFeatureProjection_smooth_ae
      period hPeriod data direction,
     Lp.coeFn_zero GlobalLLAuxMeasureFeatureFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
    with point hProjection hLpZero
  rw [hProjection, hLpZero]
  change WithLp.toLp 2
      (globalCandidateALLAuxWeight period hPeriod data point • direction.1 point,
        globalCandidateALLAuxPTWeight period hPeriod data point •
          differentialLLAuxMetricDirectionPT period hPeriod direction.1 point) = 0
  rw [globalCandidateALLAuxWeight_eq_zero period hPeriod data hZero point,
    globalCandidateALLAuxPTWeight_eq_zero period hPeriod data hZero point]
  simp

theorem globalCandidateALLAuxMeasureFeatureProjection_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (direction : GlobalLLAuxMeasureGraphHilbert period hPeriod data) :
    globalCandidateALLAuxMeasureFeatureProjection period hPeriod data direction = 0 := by
  let projection :=
    globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
  have hFunctions :
      (fun value : GlobalLLAuxMeasureGraphHilbert period hPeriod data =>
        projection value) = fun _ => 0 :=
    (globalCandidateALLAuxMeasureSmoothEmbedding_denseRange
      period hPeriod data).equalizer
        projection.continuous continuous_const (by
          funext smooth
          exact globalCandidateALLAuxMeasureFeatureProjection_smooth_eq_zero
            period hPeriod data hZero smooth)
  exact congrFun hFunctions direction

theorem globalCandidateALLAuxMeasureGraphRieszOperator_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (direction : GlobalLLAuxMeasureGraphHilbert period hPeriod data) :
    globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data direction = 0 := by
  letI : CompleteSpace (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  unfold globalCandidateALLAuxMeasureGraphRieszOperator
  rw [ContinuousLinearMap.comp_apply,
    globalCandidateALLAuxMeasureFeatureProjection_eq_zero
      period hPeriod data hZero direction]
  exact map_zero _

theorem globalCandidateAFullLLCrossVProjection_smooth_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLCrossVProjection period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis direction) = 0 := by
  apply Lp.ext
  filter_upwards
    [globalCandidateAFullLLCrossVProjection_smooth_ae
      period hPeriod data analysis direction,
     Lp.coeFn_zero GlobalFullLLCrossFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
    with point hProjection hLpZero
  rw [hProjection, hLpZero]
  unfold globalCandidateAFullLLCrossV
  rw [hZero, throatPTPullback_zero]
  have hPointZero :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod LLFieldFiber) point = 0 := rfl
  rw [hPointZero]
  simp [throatDerivativePairing]

theorem globalCandidateAFullLLCrossVProjection_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (direction : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLCrossVProjection period hPeriod data analysis direction = 0 := by
  let projection :=
    globalCandidateAFullLLCrossVProjection period hPeriod data analysis
  have hFunctions :
      (fun value : GlobalFullLLGraphHilbert period hPeriod data analysis =>
        projection value) = fun _ => 0 :=
    (globalCandidateAFullLLSmoothEmbedding_denseRange
      period hPeriod data analysis).equalizer
        projection.continuous continuous_const (by
          funext smooth
          exact globalCandidateAFullLLCrossVProjection_smooth_eq_zero
            period hPeriod data analysis hZero smooth)
  exact congrFun hFunctions direction

theorem globalCandidateAFullLLContinuousHessian_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLContinuousHessian period hPeriod
        data analysis first second =
      inner Real
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis first)
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis second) := by
  unfold globalCandidateAFullLLContinuousHessian
  rw [globalCandidateALLAuxMeasureGraphRieszOperator_eq_zero
      period hPeriod data hZero,
    globalCandidateAFullLLCrossVProjection_eq_zero
      period hPeriod data analysis hZero first,
    globalCandidateAFullLLCrossVProjection_eq_zero
      period hPeriod data analysis hZero second]
  simp

theorem globalCandidateAFullLLGraphRieszOperator_ker_eq_fieldProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    LinearMap.ker
        (globalCandidateAFullLLGraphRieszOperator period hPeriod
          data analysis).toLinearMap =
      LinearMap.ker
        (globalCandidateAFullLLFieldProjection period hPeriod
          data analysis).toLinearMap := by
  ext direction
  simp only [LinearMap.mem_ker]
  constructor
  · intro hRiesz
    change globalCandidateAFullLLGraphRieszOperator period hPeriod
      data analysis direction = 0 at hRiesz
    have hPairing :=
      globalCandidateAFullLLGraphRieszOperator_pairing
        period hPeriod data analysis direction direction
    rw [hRiesz] at hPairing
    have hLeft :
        inner Real
          (0 : GlobalFullLLGraphHilbert period hPeriod data analysis)
          direction = 0 := by
      exact inner_zero_left direction
    rw [hLeft,
      globalCandidateAFullLLContinuousHessian_zeroFlux
        period hPeriod data analysis hZero] at hPairing
    exact inner_self_eq_zero.mp hPairing.symm
  · intro hField
    change globalCandidateAFullLLFieldProjection period hPeriod
      data analysis direction = 0 at hField
    exact LinearMap.mem_ker.mp
      ((globalCandidateAFullLLGraphRieszOperator_mem_ker_iff
        period hPeriod data analysis direction).2 (fun test => by
          rw [globalCandidateAFullLLContinuousHessian_zeroFlux
            period hPeriod data analysis hZero, hField, inner_zero_left]))

theorem globalCandidateAFullLLCrossGraphToL2_fieldOnly_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (field : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    globalCandidateAFullLLCrossGraphToL2 period hPeriod data
        ((0, field) : GlobalFullLLSmooth period hPeriod analysis) = 0 := by
  apply Lp.ext
  filter_upwards
    [globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data
      ((0, field) : GlobalFullLLSmooth period hPeriod analysis),
     Lp.coeFn_zero GlobalFullLLCrossGraphFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
    with point hGraph hLpZero
  rw [hGraph, hLpZero]
  unfold globalCandidateAFullLLCrossGraphFeature
    globalCandidateAFullLLCrossU globalCandidateAFullLLCrossV
  rw [hZero, throatPTPullback_zero]
  have hMetricZero :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod LLMetricFiber) point = 0 := rfl
  have hScalarZero :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod Real) point = 0 := rfl
  have hFieldZero :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod LLFieldFiber) point = 0 := rfl
  have hAuxFirst :
      (0 : GlobalLLAuxMeasureSmooth period hPeriod).1 = 0 := rfl
  have hAuxSecond :
      (0 : GlobalLLAuxMeasureSmooth period hPeriod).2 = 0 := rfl
  rw [hAuxFirst, hAuxSecond]
  rw [hMetricZero, hScalarZero, hFieldZero]
  simp [differentialLLAuxMetricDirectionPT, throatDerivativePairing]
  constructor
  · rw [hMetricZero]
    exact inner_zero_right _
  · exact hScalarZero

/-- Ambient copy of the completed LL-field factor with every other coordinate
set to zero. -/
def globalCandidateAFullLLFieldAmbient
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (field : LLH1Space period hPeriod (analysis.llH1Data period hPeriod)) :
    GlobalFullLLGraphAmbient period hPeriod data analysis :=
  WithLp.toLp 2
    (WithLp.toLp 2
      (0, field),
      0)

theorem globalCandidateAFullLLFieldAmbient_continuous
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Continuous
      (globalCandidateAFullLLFieldAmbient period hPeriod data analysis) := by
  unfold globalCandidateAFullLLFieldAmbient
  have hBase : Continuous (fun field :
      LLH1Space period hPeriod (analysis.llH1Data period hPeriod) =>
      WithLp.toLp 2
        ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), field)) :=
    (WithLp.prodContinuousLinearEquiv 2 Real
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data)
      (LLH1Space period hPeriod (analysis.llH1Data period hPeriod))).symm.continuous.comp
        (continuous_const.prodMk continuous_id)
  exact
    (WithLp.prodContinuousLinearEquiv 2 Real
      (GlobalFullLLBaseHilbert period hPeriod data analysis)
      (Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).symm.continuous.comp
      (hBase.prodMk continuous_const)

theorem globalCandidateAFullLLFieldAmbient_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (field : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    globalCandidateAFullLLFieldAmbient period hPeriod data analysis
        (llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) field) =
      globalCandidateAFullLLGraphAmbientLinearMap period hPeriod data analysis
        ((0, field) : GlobalFullLLSmooth period hPeriod analysis) := by
  unfold globalCandidateAFullLLFieldAmbient
  change WithLp.toLp 2
      (WithLp.toLp 2
        ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data),
          llH1SmoothEmbedding period hPeriod
            (analysis.llH1Data period hPeriod) field),
        0) =
    WithLp.toLp 2
      (WithLp.toLp 2
        (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data 0,
          llH1SmoothEmbedding period hPeriod
            (analysis.llH1Data period hPeriod) field),
        globalCandidateAFullLLCrossGraphToL2 period hPeriod data
          ((0, field) : GlobalFullLLSmooth period hPeriod analysis))
  rw [(globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data).map_zero,
    globalCandidateAFullLLCrossGraphToL2_fieldOnly_eq_zero
      period hPeriod data analysis hZero field]

theorem globalCandidateAFullLLFieldAmbient_mem
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (field : LLH1Space period hPeriod (analysis.llH1Data period hPeriod)) :
    globalCandidateAFullLLFieldAmbient period hPeriod data analysis field ∈
      globalCandidateAFullLLGraphSubmodule period hPeriod data analysis := by
  refine DenseRange.induction_on
    (llH1SmoothEmbedding_denseRange period hPeriod
      (analysis.llH1Data period hPeriod))
    (p := fun value =>
      globalCandidateAFullLLFieldAmbient period hPeriod data analysis value ∈
        globalCandidateAFullLLGraphSubmodule period hPeriod data analysis)
    field ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage
      (globalCandidateAFullLLFieldAmbient_continuous
        period hPeriod data analysis)
  · intro smooth
    rw [globalCandidateAFullLLFieldAmbient_smooth
      period hPeriod data analysis hZero smooth]
    exact (LinearMap.range
      (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
        data analysis)).le_topologicalClosure
          (LinearMap.mem_range_self
            (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
              data analysis)
            ((0, smooth) : GlobalFullLLSmooth period hPeriod analysis))

/-- On the zero-flux branch the completed LL-field factor embeds back into
the full graph with all auxiliary, measure and cross coordinates zero. -/
def globalCandidateAFullLLFieldInjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    LLH1Space period hPeriod (analysis.llH1Data period hPeriod) →ₗ[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis where
  toFun field :=
    ⟨globalCandidateAFullLLFieldAmbient period hPeriod data analysis field,
      globalCandidateAFullLLFieldAmbient_mem
        period hPeriod data analysis hZero field⟩
  map_add' first second := by
    apply Subtype.ext
    unfold globalCandidateAFullLLFieldAmbient
    change WithLp.toLp 2
        (WithLp.toLp 2
          ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data),
            first + second), 0) =
      WithLp.toLp 2
          (WithLp.toLp 2
            ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), first), 0) +
        WithLp.toLp 2
          (WithLp.toLp 2
            ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), second), 0)
    rw [← WithLp.toLp_add]
    congr 1
    apply Prod.ext
    · change WithLp.toLp 2
          ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data),
            first + second) =
        WithLp.toLp 2
            ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), first) +
          WithLp.toLp 2
            ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), second)
      rw [← WithLp.toLp_add]
      simp
    · simp
  map_smul' scalar field := by
    apply Subtype.ext
    unfold globalCandidateAFullLLFieldAmbient
    change WithLp.toLp 2
        (WithLp.toLp 2
          ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data),
            scalar • field), 0) =
      scalar • WithLp.toLp 2
        (WithLp.toLp 2
          ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), field), 0)
    rw [← WithLp.toLp_smul]
    congr 1
    apply Prod.ext
    · change WithLp.toLp 2
          ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data),
            scalar • field) =
        scalar • WithLp.toLp 2
          ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), field)
      rw [← WithLp.toLp_smul]
      simp
    · simp

@[simp]
theorem globalCandidateAFullLLFieldProjection_injection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (field : LLH1Space period hPeriod (analysis.llH1Data period hPeriod)) :
    globalCandidateAFullLLFieldProjection period hPeriod data analysis
        (globalCandidateAFullLLFieldInjection period hPeriod
          data analysis hZero field) = field :=
  rfl

theorem globalCandidateAFullLLFieldProjection_surjective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    Function.Surjective
      (globalCandidateAFullLLFieldProjection period hPeriod data analysis) := by
  intro field
  exact ⟨globalCandidateAFullLLFieldInjection period hPeriod
    data analysis hZero field,
    globalCandidateAFullLLFieldProjection_injection
      period hPeriod data analysis hZero field⟩

/-- The zero-flux field injection, bundled as a continuous linear map. -/
def globalCandidateAFullLLFieldInjectionCLM
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    LLH1Space period hPeriod (analysis.llH1Data period hPeriod) →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis where
  toLinearMap := globalCandidateAFullLLFieldInjection period hPeriod
    data analysis hZero
  cont := (globalCandidateAFullLLFieldAmbient_continuous
    period hPeriod data analysis).subtype_mk _

theorem globalCandidateAFullLLFieldInjection_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (field : LLH1Space period hPeriod (analysis.llH1Data period hPeriod))
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    inner Real
        (globalCandidateAFullLLFieldInjection period hPeriod
          data analysis hZero field) state =
      inner Real field
        (globalCandidateAFullLLFieldProjection
          period hPeriod data analysis state) := by
  change inner Real
      (WithLp.toLp 2
        (WithLp.toLp 2
          ((0 : GlobalLLAuxMeasureGraphHilbert period hPeriod data), field), 0))
      state.1 =
    inner Real field (WithLp.ofLp (WithLp.ofLp state.1).1).2
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp

theorem globalCandidateAFullLLGraphRieszOperator_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis state =
      globalCandidateAFullLLFieldInjection period hPeriod data analysis hZero
        (globalCandidateAFullLLFieldProjection
          period hPeriod data analysis state) := by
  apply ext_inner_right Real
  intro test
  rw [globalCandidateAFullLLGraphRieszOperator_pairing,
    globalCandidateAFullLLContinuousHessian_zeroFlux
      period hPeriod data analysis hZero,
    globalCandidateAFullLLFieldInjection_inner
      period hPeriod data analysis hZero]

/-- Exact reduction space: quotient of the full LL graph by the directions
invisible to the positive LL-field projection. -/
abbrev GlobalCandidateAFullLLFieldQuotient
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalFullLLGraphHilbert period hPeriod data analysis ⧸
    (globalCandidateAFullLLFieldProjection
      period hPeriod data analysis).ker

/-- The field projection descended to its exact kernel quotient. -/
def globalCandidateAFullLLFieldQuotientProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis →L[Real]
      LLH1Space period hPeriod (analysis.llH1Data period hPeriod) :=
  (globalCandidateAFullLLFieldProjection
      period hPeriod data analysis).ker.liftQL
    (globalCandidateAFullLLFieldProjection period hPeriod data analysis) le_rfl

/-- On the zero-flux branch, the field injection followed by the quotient map. -/
def globalCandidateAFullLLFieldQuotientInjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    LLH1Space period hPeriod (analysis.llH1Data period hPeriod) →L[Real]
      GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis :=
  (globalCandidateAFullLLFieldProjection
      period hPeriod data analysis).ker.mkQL.comp
    (globalCandidateAFullLLFieldInjectionCLM
      period hPeriod data analysis hZero)

@[simp]
theorem globalCandidateAFullLLFieldQuotientProjection_injection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (field : LLH1Space period hPeriod (analysis.llH1Data period hPeriod)) :
    globalCandidateAFullLLFieldQuotientProjection period hPeriod data analysis
        (globalCandidateAFullLLFieldQuotientInjection
          period hPeriod data analysis hZero field) = field := by
  exact globalCandidateAFullLLFieldProjection_injection
    period hPeriod data analysis hZero field

@[simp]
theorem globalCandidateAFullLLFieldQuotientInjection_projection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (state : GlobalCandidateAFullLLFieldQuotient
      period hPeriod data analysis) :
    globalCandidateAFullLLFieldQuotientInjection period hPeriod
        data analysis hZero
        (globalCandidateAFullLLFieldQuotientProjection
          period hPeriod data analysis state) = state := by
  rcases (globalCandidateAFullLLFieldProjection period hPeriod
    data analysis).ker.mkQ_surjective state with ⟨representative, rfl⟩
  apply (Submodule.Quotient.eq _).2
  change globalCandidateAFullLLFieldProjection period hPeriod data analysis
      (globalCandidateAFullLLFieldInjection period hPeriod data analysis hZero
          (globalCandidateAFullLLFieldProjection
            period hPeriod data analysis representative) - representative) = 0
  rw [map_sub, globalCandidateAFullLLFieldProjection_injection]
  exact sub_self _

/-- At zero flux, the exact full-graph quotient is continuously linearly
equivalent to the existing positive LL-field completion. -/
def globalCandidateAFullLLFieldQuotientEquiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis ≃L[Real]
      LLH1Space period hPeriod (analysis.llH1Data period hPeriod) :=
  ContinuousLinearEquiv.equivOfInverse
    (globalCandidateAFullLLFieldQuotientProjection
      period hPeriod data analysis)
    (globalCandidateAFullLLFieldQuotientInjection
      period hPeriod data analysis hZero)
    (globalCandidateAFullLLFieldQuotientInjection_projection
      period hPeriod data analysis hZero)
    (globalCandidateAFullLLFieldQuotientProjection_injection
      period hPeriod data analysis hZero)

/-- The full graph Riesz operator descended to the exact radical quotient. -/
def globalCandidateAFullLLFieldQuotientRieszOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis →L[Real]
      GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis :=
  (globalCandidateAFullLLFieldQuotientInjection
      period hPeriod data analysis hZero).comp
    (globalCandidateAFullLLFieldQuotientProjection
      period hPeriod data analysis)

@[simp]
theorem globalCandidateAFullLLFieldQuotientRieszOperator_mkQL
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
        data analysis hZero
        ((globalCandidateAFullLLFieldProjection
          period hPeriod data analysis).ker.mkQL state) =
      (globalCandidateAFullLLFieldProjection
          period hPeriod data analysis).ker.mkQL
        (globalCandidateAFullLLGraphRieszOperator
          period hPeriod data analysis state) := by
  change (globalCandidateAFullLLFieldProjection
      period hPeriod data analysis).ker.mkQ
        (globalCandidateAFullLLFieldInjection period hPeriod data analysis hZero
          (globalCandidateAFullLLFieldProjection
            period hPeriod data analysis state)) =
    (globalCandidateAFullLLFieldProjection
      period hPeriod data analysis).ker.mkQ
        (globalCandidateAFullLLGraphRieszOperator
          period hPeriod data analysis state)
  apply (Submodule.Quotient.eq _).2
  change globalCandidateAFullLLFieldProjection period hPeriod data analysis
      (globalCandidateAFullLLFieldInjection period hPeriod data analysis hZero
          (globalCandidateAFullLLFieldProjection
            period hPeriod data analysis state) -
        globalCandidateAFullLLGraphRieszOperator
          period hPeriod data analysis state) = 0
  rw [map_sub, globalCandidateAFullLLFieldProjection_injection]
  have hProjection := congrArg
    (globalCandidateAFullLLFieldProjection period hPeriod data analysis)
    (globalCandidateAFullLLGraphRieszOperator_zeroFlux
      period hPeriod data analysis hZero state)
  rw [globalCandidateAFullLLFieldProjection_injection] at hProjection
  rw [hProjection, sub_self]

theorem globalCandidateAFullLLFieldQuotientRieszOperator_eq_id
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
        data analysis hZero =
      ContinuousLinearMap.id Real
        (GlobalCandidateAFullLLFieldQuotient
          period hPeriod data analysis) := by
  apply ContinuousLinearMap.ext
  intro state
  exact globalCandidateAFullLLFieldQuotientInjection_projection
    period hPeriod data analysis hZero state

theorem globalCandidateAFullLLFieldQuotientRieszOperator_ker_eq_bot
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    LinearMap.ker
        (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
          data analysis hZero).toLinearMap = ⊥ := by
  rw [globalCandidateAFullLLFieldQuotientRieszOperator_eq_id
    period hPeriod data analysis hZero]
  exact LinearMap.ker_id

theorem globalCandidateAFullLLFieldQuotientRieszOperator_range_eq_top
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    LinearMap.range
        (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
          data analysis hZero).toLinearMap = ⊤ := by
  rw [globalCandidateAFullLLFieldQuotientRieszOperator_eq_id
    period hPeriod data analysis hZero]
  exact LinearMap.range_id

abbrev GlobalCandidateAFullLLFieldQuotientRieszCokernel
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :=
  GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis ⧸
    LinearMap.range
      (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
        data analysis hZero).toLinearMap

theorem globalCandidateAFullLLFieldQuotientRieszOperator_fredholm_criterion
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    IsClosed
        (LinearMap.range
          (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
            data analysis hZero).toLinearMap :
              Set (GlobalCandidateAFullLLFieldQuotient
                period hPeriod data analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
            data analysis hZero).toLinearMap) ∧
      FiniteDimensional Real
        (GlobalCandidateAFullLLFieldQuotientRieszCokernel
          period hPeriod data analysis hZero) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [globalCandidateAFullLLFieldQuotientRieszOperator_range_eq_top
      period hPeriod data analysis hZero]
    exact isClosed_univ
  · rw [globalCandidateAFullLLFieldQuotientRieszOperator_ker_eq_bot
      period hPeriod data analysis hZero]
    infer_instance
  · change FiniteDimensional Real
      (GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis ⧸
        LinearMap.range
          (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
            data analysis hZero).toLinearMap)
    rw [globalCandidateAFullLLFieldQuotientRieszOperator_range_eq_top
      period hPeriod data analysis hZero]
    apply FiniteDimensional.of_injective
      (0 :
        (GlobalCandidateAFullLLFieldQuotient period hPeriod data analysis ⧸
            (⊤ : Submodule Real
              (GlobalCandidateAFullLLFieldQuotient
                period hPeriod data analysis))) →ₗ[Real]
          (Fin 0 → Real))
    intro first second _
    exact Subsingleton.elim first second

def globalCandidateAFullLLFieldQuotientRieszIndex
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) : Int :=
  (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
    data analysis hZero).toLinearMap.index

theorem globalCandidateAFullLLFieldQuotientRieszIndex_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0) :
    globalCandidateAFullLLFieldQuotientRieszIndex period hPeriod
      data analysis hZero = 0 := by
  unfold globalCandidateAFullLLFieldQuotientRieszIndex
  rw [LinearMap.index_of_surjective,
    globalCandidateAFullLLFieldQuotientRieszOperator_ker_eq_bot
      period hPeriod data analysis hZero]
  · simp
  · rw [← LinearMap.range_eq_top]
    exact globalCandidateAFullLLFieldQuotientRieszOperator_range_eq_top
      period hPeriod data analysis hZero

/-- Terminal on-shell form: LL stationarity itself supplies the zero-flux
background used by the quotient Fredholm criterion. -/
theorem globalCandidateAFullLLFieldQuotientRieszOperator_fredholm_criterion_of_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :
    let hZero :=
      llField_eq_zero_of_stationary period hPeriod
        (data.boundary.llFields period hPeriod) hStationary
    IsClosed
        (LinearMap.range
          (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
            data analysis hZero).toLinearMap :
              Set (GlobalCandidateAFullLLFieldQuotient
                period hPeriod data analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (globalCandidateAFullLLFieldQuotientRieszOperator period hPeriod
            data analysis hZero).toLinearMap) ∧
      FiniteDimensional Real
        (GlobalCandidateAFullLLFieldQuotientRieszCokernel
          period hPeriod data analysis hZero) := by
  dsimp only
  exact
    globalCandidateAFullLLFieldQuotientRieszOperator_fredholm_criterion
      period hPeriod data analysis
        (llField_eq_zero_of_stationary period hPeriod
          (data.boundary.llFields period hPeriod) hStationary)

/-- The on-shell quotient index is zero directly from the LL stationarity
equations, without a separately supplied zero-flux hypothesis. -/
theorem globalCandidateAFullLLFieldQuotientRieszIndex_zero_of_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :
    let hZero :=
      llField_eq_zero_of_stationary period hPeriod
        (data.boundary.llFields period hPeriod) hStationary
    globalCandidateAFullLLFieldQuotientRieszIndex period hPeriod
      data analysis hZero = 0 := by
  dsimp only
  exact
    globalCandidateAFullLLFieldQuotientRieszIndex_zero period hPeriod
      data analysis
        (llField_eq_zero_of_stationary period hPeriod
          (data.boundary.llFields period hPeriod) hStationary)

end
end P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
end JanusFormal

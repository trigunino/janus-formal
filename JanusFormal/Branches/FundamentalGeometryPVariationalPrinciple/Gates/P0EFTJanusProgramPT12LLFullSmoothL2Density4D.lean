import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLSmoothL2Density4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

/-! The full three-slot smooth LL core is dense in its product L² carrier. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullSmoothL2Density4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

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

local instance : MetrizableSpace (EffectiveThroat period hPeriod) :=
  Manifold.metrizableSpace throatCoverModelWithCorners _

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

variable (Fiber : Type*) [NormedAddCommGroup Fiber]
  [NormedSpace Real Fiber] [CompleteSpace Fiber]

/-- Inclusion of an arbitrary smooth throat field into canonical L². -/
def smoothThroatToL2
    (field : SmoothThroatField period hPeriod Fiber) :
    Lp Fiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (smoothThroatField_memLp period hPeriod Fiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field).toLp field.toFun

private def continuousToL2 :
    C(EffectiveThroat period hPeriod, Fiber) →L[Real]
      Lp Fiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ContinuousMap.toLp (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) Real

private theorem continuousToL2_denseRange :
    DenseRange (continuousToL2 period hPeriod Fiber) := by
  exact ContinuousMap.toLp_denseRange Fiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) Real
    (by norm_num : (2 : ENNReal) ≠ (⊤ : ENNReal))

private def approximationRadius (index : Nat) : Real :=
  1 / (index + 1 : Real)

private theorem approximationRadius_pos (index : Nat) :
    0 < approximationRadius index := by
  unfold approximationRadius
  positivity

private theorem exists_smoothApproximation
    (continuousField : C(EffectiveThroat period hPeriod, Fiber))
    (index : Nat) :
    ∃ smoothField : SmoothThroatField period hPeriod Fiber,
      ∀ point,
        dist (continuousField point) (smoothField point) <
          approximationRadius index := by
  obtain ⟨approximation, hApproximation, _⟩ :=
    continuousField.continuous.exists_contMDiff_approx
      throatCoverModelWithCorners (⊤ : ℕ∞)
      (continuous_const : Continuous
        (fun _ : EffectiveThroat period hPeriod => approximationRadius index))
      (fun _ => approximationRadius_pos index)
  refine ⟨{ toFun := approximation, contMDiff_toFun := approximation.contMDiff }, ?_⟩
  intro point
  have hPoint := hApproximation point
  rw [dist_comm] at hPoint
  exact hPoint

private def smoothApproximation
    (continuousField : C(EffectiveThroat period hPeriod, Fiber))
    (index : Nat) : SmoothThroatField period hPeriod Fiber :=
  Classical.choose (exists_smoothApproximation period hPeriod Fiber continuousField index)

private def smoothApproximationContinuousMap
    (continuousField : C(EffectiveThroat period hPeriod, Fiber))
    (index : Nat) : C(EffectiveThroat period hPeriod, Fiber) :=
  ⟨smoothApproximation period hPeriod Fiber continuousField index,
    (smoothApproximation period hPeriod Fiber continuousField index)
      |>.contMDiff_toFun.continuous⟩

private theorem smoothApproximationContinuousMap_dist_le
    (continuousField : C(EffectiveThroat period hPeriod, Fiber))
    (index : Nat) :
    dist (smoothApproximationContinuousMap period hPeriod Fiber continuousField index)
        continuousField ≤ approximationRadius index := by
  apply (ContinuousMap.dist_le (approximationRadius_pos index).le).2
  intro point
  have hApproximation :=
    (Classical.choose_spec
      (exists_smoothApproximation period hPeriod Fiber continuousField index)) point
  rw [dist_comm] at hApproximation
  exact le_of_lt hApproximation

private theorem smoothApproximationContinuousMap_tendsto
    (continuousField : C(EffectiveThroat period hPeriod, Fiber)) :
    Tendsto (smoothApproximationContinuousMap period hPeriod Fiber continuousField)
      atTop (𝓝 continuousField) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => dist_nonneg)
    (Filter.Eventually.of_forall fun index =>
      smoothApproximationContinuousMap_dist_le
        period hPeriod Fiber continuousField index)
  change Tendsto (fun index : Nat => 1 / ((index : Real) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private theorem continuousToL2_smoothApproximation
    (continuousField : C(EffectiveThroat period hPeriod, Fiber))
    (index : Nat) :
    continuousToL2 period hPeriod Fiber
        (smoothApproximationContinuousMap period hPeriod Fiber continuousField index) =
      smoothThroatToL2 period hPeriod Fiber
        (smoothApproximation period hPeriod Fiber continuousField index) := by
  rw [Lp.ext_iff]
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := (2 : ENNReal))
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (𝕜 := Real)
      (smoothApproximationContinuousMap period hPeriod Fiber continuousField index),
     (smoothThroatField_memLp period hPeriod Fiber
       (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
       (smoothApproximation period hPeriod Fiber continuousField index)).coeFn_toLp]
    with point hContinuous hSmooth
  calc
    _ = smoothApproximationContinuousMap period hPeriod Fiber continuousField index point :=
      hContinuous
    _ = smoothApproximation period hPeriod Fiber continuousField index point := rfl
    _ = _ := hSmooth.symm

private theorem smoothApproximation_tendsto_l2
    (continuousField : C(EffectiveThroat period hPeriod, Fiber)) :
    Tendsto
      (fun index => smoothThroatToL2 period hPeriod Fiber
        (smoothApproximation period hPeriod Fiber continuousField index))
      atTop (𝓝 (continuousToL2 period hPeriod Fiber continuousField)) := by
  have hContinuous : Tendsto
      (fun index => continuousToL2 period hPeriod Fiber
        (smoothApproximationContinuousMap period hPeriod Fiber continuousField index))
      atTop (𝓝 (continuousToL2 period hPeriod Fiber continuousField)) :=
    (continuousToL2 period hPeriod Fiber).continuous.continuousAt
      |>.tendsto.comp
        (smoothApproximationContinuousMap_tendsto
          period hPeriod Fiber continuousField)
  exact hContinuous.congr'
    (Filter.Eventually.of_forall fun index =>
      continuousToL2_smoothApproximation
        period hPeriod Fiber continuousField index)

/-- Smooth throat fields of any complete normed real fiber are dense in canonical L². -/
theorem smoothThroatToL2_denseRange :
    DenseRange (smoothThroatToL2 period hPeriod Fiber) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (continuousToL2 period hPeriod Fiber)) :=
    continuousToL2_denseRange period hPeriod Fiber value
  apply (closure_minimal ?_ isClosed_closure) hContinuous
  rintro value ⟨continuousField, rfl⟩
  apply mem_closure_of_tendsto
    (smoothApproximation_tendsto_l2 period hPeriod Fiber continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨smoothApproximation period hPeriod Fiber continuousField index, rfl⟩

/-- The exact L² carrier for the three smooth LL slots. -/
abbrev FullLLL2
    := (Lp LLMetricFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
        Lp Real (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ×
      Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The three smooth slots embedded into their product L² carrier. -/
def fullLLSmoothToL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    FullLLL2 period hPeriod :=
  ((smoothThroatToL2 period hPeriod LLMetricFiber direction.1.1,
    smoothThroatToL2 period hPeriod Real direction.1.2),
    llSmoothToL2 period hPeriod direction.2.toTest)

/-- The full three-slot smooth core has dense range in product L². -/
theorem fullLLSmoothToL2_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange (fullLLSmoothToL2 period hPeriod analysis) := by
  have hField : DenseRange
      (fun direction : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod) =>
        llSmoothToL2 period hPeriod direction.toTest) := by
    have hRange :
        Set.range (fun direction : LLH1Smooth period hPeriod
            (analysis.llH1Data period hPeriod) =>
          llSmoothToL2 period hPeriod direction.toTest) =
          Set.range (llSmoothToL2 period hPeriod) := by
      ext value
      constructor
      · rintro ⟨direction, rfl⟩
        exact ⟨direction.toTest, rfl⟩
      · rintro ⟨test, rfl⟩
        exact ⟨LLH1Smooth.ofTest period hPeriod
          (analysis.llH1Data period hPeriod) test, rfl⟩
    simpa only [DenseRange, hRange] using
      (llSmoothToL2_denseRange period hPeriod)
  change DenseRange (Prod.map
    (Prod.map (smoothThroatToL2 period hPeriod LLMetricFiber)
      (smoothThroatToL2 period hPeriod Real))
    (fun direction : LLH1Smooth period hPeriod
        (analysis.llH1Data period hPeriod) =>
      llSmoothToL2 period hPeriod direction.toTest))
  exact ((smoothThroatToL2_denseRange period hPeriod LLMetricFiber).prodMap
    (smoothThroatToL2_denseRange period hPeriod Real)).prodMap hField

end
end P0EFTJanusProgramPT12LLFullSmoothL2Density4D
end JanusFormal

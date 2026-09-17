import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

/-! Smooth LL-field tests are dense in L² for the canonical throat volume. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLSmoothL2Density4D

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
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D

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

/-- Inclusion of a smooth LL-field test into the canonical throat L² space. -/
def llSmoothToL2
    (field : LLWeakTestSpace period hPeriod) :
    Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (smoothThroatField_memLp period hPeriod LLFieldFiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field).toLp field.toFun

/-- Continuous LL fields are dense in canonical throat L². -/
def continuousToLLL2 :
    C(EffectiveThroat period hPeriod, LLFieldFiber) →L[Real]
      Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ContinuousMap.toLp (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) Real

theorem continuousToLLL2_denseRange :
    DenseRange (continuousToLLL2 period hPeriod) := by
  exact ContinuousMap.toLp_denseRange LLFieldFiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) Real
    (by norm_num : (2 : ENNReal) ≠ (⊤ : ENNReal))

private def approximationRadius (index : Nat) : Real :=
  1 / (index + 1 : Real)

private theorem approximationRadius_pos (index : Nat) :
    0 < approximationRadius index := by
  unfold approximationRadius
  positivity

private theorem exists_smoothApproximation
    (continuousField : C(EffectiveThroat period hPeriod, LLFieldFiber))
    (index : Nat) :
    ∃ smoothField : LLWeakTestSpace period hPeriod,
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
    (continuousField : C(EffectiveThroat period hPeriod, LLFieldFiber))
    (index : Nat) : LLWeakTestSpace period hPeriod :=
  Classical.choose (exists_smoothApproximation period hPeriod continuousField index)

private def smoothApproximationContinuousMap
    (continuousField : C(EffectiveThroat period hPeriod, LLFieldFiber))
    (index : Nat) : C(EffectiveThroat period hPeriod, LLFieldFiber) :=
  ⟨smoothApproximation period hPeriod continuousField index,
    (smoothApproximation period hPeriod continuousField index)
      |>.contMDiff_toFun.continuous⟩

private theorem smoothApproximationContinuousMap_dist_le
    (continuousField : C(EffectiveThroat period hPeriod, LLFieldFiber))
    (index : Nat) :
    dist (smoothApproximationContinuousMap period hPeriod continuousField index)
        continuousField ≤ approximationRadius index := by
  apply (ContinuousMap.dist_le (approximationRadius_pos index).le).2
  intro point
  have hApproximation :=
    (Classical.choose_spec
      (exists_smoothApproximation period hPeriod continuousField index)) point
  rw [dist_comm] at hApproximation
  exact le_of_lt hApproximation

private theorem smoothApproximationContinuousMap_tendsto
    (continuousField : C(EffectiveThroat period hPeriod, LLFieldFiber)) :
    Tendsto (smoothApproximationContinuousMap period hPeriod continuousField)
      atTop (𝓝 continuousField) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => dist_nonneg)
    (Filter.Eventually.of_forall fun index =>
      smoothApproximationContinuousMap_dist_le
        period hPeriod continuousField index)
  change Tendsto (fun index : Nat => 1 / ((index : Real) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private theorem continuousToLLL2_smoothApproximation
    (continuousField : C(EffectiveThroat period hPeriod, LLFieldFiber))
    (index : Nat) :
    continuousToLLL2 period hPeriod
        (smoothApproximationContinuousMap period hPeriod continuousField index) =
      llSmoothToL2 period hPeriod
        (smoothApproximation period hPeriod continuousField index) := by
  rw [Lp.ext_iff]
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := (2 : ENNReal))
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (𝕜 := Real)
      (smoothApproximationContinuousMap period hPeriod continuousField index),
     (smoothThroatField_memLp period hPeriod LLFieldFiber
       (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
       (smoothApproximation period hPeriod continuousField index)).coeFn_toLp]
    with point hContinuous hSmooth
  calc
    _ = smoothApproximationContinuousMap period hPeriod continuousField index point :=
      hContinuous
    _ = smoothApproximation period hPeriod continuousField index point := rfl
    _ = _ := hSmooth.symm

private theorem smoothApproximation_tendsto_l2
    (continuousField : C(EffectiveThroat period hPeriod, LLFieldFiber)) :
    Tendsto
      (fun index => llSmoothToL2 period hPeriod
        (smoothApproximation period hPeriod continuousField index))
      atTop (𝓝 (continuousToLLL2 period hPeriod continuousField)) := by
  have hContinuous : Tendsto
      (fun index => continuousToLLL2 period hPeriod
        (smoothApproximationContinuousMap period hPeriod continuousField index))
      atTop (𝓝 (continuousToLLL2 period hPeriod continuousField)) :=
    (continuousToLLL2 period hPeriod).continuous.continuousAt
      |>.tendsto.comp
        (smoothApproximationContinuousMap_tendsto
          period hPeriod continuousField)
  exact hContinuous.congr'
    (Filter.Eventually.of_forall fun index =>
      continuousToLLL2_smoothApproximation
        period hPeriod continuousField index)

/-- Smooth LL-field tests are dense in the actual canonical throat L². -/
theorem llSmoothToL2_denseRange :
    DenseRange (llSmoothToL2 period hPeriod) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (continuousToLLL2 period hPeriod)) :=
    continuousToLLL2_denseRange period hPeriod value
  apply (closure_minimal ?_ isClosed_closure) hContinuous
  rintro value ⟨continuousField, rfl⟩
  apply mem_closure_of_tendsto
    (smoothApproximation_tendsto_l2 period hPeriod continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨smoothApproximation period hPeriod continuousField index, rfl⟩

end
end P0EFTJanusProgramPT12LLSmoothL2Density4D
end JanusFormal

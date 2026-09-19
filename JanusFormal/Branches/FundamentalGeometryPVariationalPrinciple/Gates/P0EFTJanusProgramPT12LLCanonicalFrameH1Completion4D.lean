import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The LL energy completion in the actual first-derivative L2 graph

Each canonical frame derivative is constructed from the manifold derivative
on smooth LL fields, bounded by the existing positive Hessian norm, and
extended continuously to that same energy completion. Values and derivatives
therefore belong jointly to the closure of the genuine smooth first-jet graph.
Smooth approximation controls all these L2 coordinates at once while keeping
the energy norm bounded.

This does not prove Rellich compactness. In particular, first-derivative graph
approximation does not imply approximation of the second-order Jacobi output,
and is not used to claim membership in the minimal closed Jacobi domain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalFrameH1Completion4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- Explicit carrier type: Lp itself is an AddSubgroup, not a type alias. -/
abbrev LLCanonicalFieldL2 : Type :=
  Lp LLFieldFiber (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The value and each actual canonical first derivative have separate L2 coordinates. -/
abbrev LLCanonicalFrameJetL2 : Type :=
  LLCanonicalFieldL2 period hPeriod ×
    (LLCanonicalFrameIndex period hPeriod → LLCanonicalFieldL2 period hPeriod)

private theorem smooth_frame_derivative_continuous
    (field : LLWeakTestSpace period hPeriod) (index : LLCanonicalFrameIndex period hPeriod) :
    Continuous (fun point => throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) field point index) :=
  (continuous_apply index).comp (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
    (canonicalDivergenceFreeLLFrame period hPeriod) field).continuous

private theorem smooth_frame_derivative_memLp
    (field : LLWeakTestSpace period hPeriod) (index : LLCanonicalFrameIndex period hPeriod) :
    MemLp (fun point => throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) field point index) (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (smooth_frame_derivative_continuous period hPeriod field index).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual smooth directional derivative as a canonical throat L2 class. -/
def llSmoothCanonicalDerivativeToL2
    (field : LLWeakTestSpace period hPeriod) (index : LLCanonicalFrameIndex period hPeriod) :
    LLCanonicalFieldL2 period hPeriod :=
  (smooth_frame_derivative_memLp period hPeriod field index).toLp
    (fun point => throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) field point index)

theorem llSmoothCanonicalDerivativeToL2_ae
    (field : LLWeakTestSpace period hPeriod) (index : LLCanonicalFrameIndex period hPeriod) :
    (llSmoothCanonicalDerivativeToL2 period hPeriod field index :
      EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      (fun point => throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field point index) :=
  (smooth_frame_derivative_memLp period hPeriod field index).coeFn_toLp

/-- Linearity is inherited from the genuine manifold frame derivative. -/
def llSmoothCanonicalDerivativeLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (index : LLCanonicalFrameIndex period hPeriod) :
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod) →ₗ[Real]
      LLCanonicalFieldL2 period hPeriod where
  toFun u := llSmoothCanonicalDerivativeToL2 period hPeriod u.toTest index
  map_add' u v := by
    apply Lp.ext
    filter_upwards
      [llSmoothCanonicalDerivativeToL2_ae period hPeriod (u + v).toTest index,
       llSmoothCanonicalDerivativeToL2_ae period hPeriod u.toTest index,
       llSmoothCanonicalDerivativeToL2_ae period hPeriod v.toTest index,
       Lp.coeFn_add (llSmoothCanonicalDerivativeToL2 period hPeriod u.toTest index)
         (llSmoothCanonicalDerivativeToL2 period hPeriod v.toTest index)]
      with point hSum hU hV hAdd
    simp only [Pi.add_apply] at hAdd
    rw [hSum, hAdd, hU, hV]
    exact congrFun (congrFun (throatFrameDerivative_add period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) u.toTest v.toTest) point) index
  map_smul' scalar u := by
    apply Lp.ext
    filter_upwards
      [llSmoothCanonicalDerivativeToL2_ae period hPeriod (scalar • u).toTest index,
       llSmoothCanonicalDerivativeToL2_ae period hPeriod u.toTest index,
       Lp.coeFn_smul scalar (llSmoothCanonicalDerivativeToL2 period hPeriod u.toTest index)]
      with point hScaled hU hSmul
    simp only [Pi.smul_apply] at hSmul
    simp only [RingHom.id_apply]
    rw [hScaled, hSmul, hU]
    exact congrFun (congrFun (throatFrameDerivative_smul period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) scalar u.toTest) point) index

theorem llSmoothCanonicalDerivativeToL2_norm_sq
    (field : LLWeakTestSpace period hPeriod) (index : LLCanonicalFrameIndex period hPeriod) :
    ‖llSmoothCanonicalDerivativeToL2 period hPeriod field index‖ ^ 2 =
      ∫ point, ‖throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field point index‖ ^ 2
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [llSmoothCanonicalDerivativeToL2_ae period hPeriod field index]
    with point hPoint
  rw [hPoint, real_inner_self_eq_norm_sq]

private theorem derivative_sq_le_frameH1SizeSq
    (field : LLWeakTestSpace period hPeriod) (index : LLCanonicalFrameIndex period hPeriod) :
    ‖llSmoothCanonicalDerivativeToL2 period hPeriod field index‖ ^ 2 ≤
      llCanonicalFrameH1SizeSq period hPeriod field := by
  rw [llSmoothCanonicalDerivativeToL2_norm_sq]
  unfold llCanonicalFrameH1SizeSq
  apply integral_mono
    (((smooth_frame_derivative_continuous period hPeriod field index).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((llCanonicalFrameH1Density_continuous period hPeriod field).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  intro point
  have hTerm : ‖throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) field point index‖ ^ 2 ≤
      throatDerivativeEnergy period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        field point := by
    unfold throatDerivativeEnergy
    exact Finset.single_le_sum
      (fun frameIndex _ => sq_nonneg ‖throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field point frameIndex‖)
      (Finset.mem_univ index)
  change _ ≤ ‖field point‖ ^ 2 + _
  linarith [sq_nonneg ‖field point‖]

/-- A single background-dependent bound works for every frame component. -/
theorem canonicalLLSmooth_frameDerivative_bound
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ∃ K : Real, 0 < K ∧ ∀ index : LLCanonicalFrameIndex period hPeriod,
      ∀ u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod),
        ‖llSmoothCanonicalDerivativeToL2 period hPeriod u.toTest index‖ ≤ K * ‖u‖ := by
  obtain ⟨B, hB, hEnergy⟩ := canonicalLLSmooth_frameH1_bound period hPeriod analysis
  refine ⟨Real.sqrt B, Real.sqrt_pos.2 hB, ?_⟩
  intro index u
  have hSq := (derivative_sq_le_frameH1SizeSq period hPeriod u.toTest index).trans (hEnergy u)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg u))).1
  rw [mul_pow, Real.sq_sqrt hB.le]
  exact hSq

/-- Continuous actual first derivative on the existing LL energy completion. -/
def canonicalLLH1FrameDerivative
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (index : LLCanonicalFrameIndex period hPeriod) :
    CanonicalLLEnergy period hPeriod analysis →L[Real] LLCanonicalFieldL2 period hPeriod :=
  LinearMap.extendOfNorm (llSmoothCanonicalDerivativeLinearMap period hPeriod analysis index)
    (llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod))

theorem canonicalLLH1FrameDerivative_agrees_on_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (index : LLCanonicalFrameIndex period hPeriod)
    (u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    canonicalLLH1FrameDerivative period hPeriod analysis index
        (llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod) u) =
      llSmoothCanonicalDerivativeToL2 period hPeriod u.toTest index := by
  apply LinearMap.extendOfNorm_eq
  · exact llH1SmoothEmbedding_denseRange period hPeriod (analysis.llH1Data period hPeriod)
  · obtain ⟨K, _, hBound⟩ := canonicalLLSmooth_frameDerivative_bound period hPeriod analysis
    refine ⟨K, ?_⟩
    intro v
    change ‖llSmoothCanonicalDerivativeToL2 period hPeriod v.toTest index‖ ≤
      K * ‖(v : LLH1Space period hPeriod (analysis.llH1Data period hPeriod))‖
    simpa only [UniformSpace.Completion.norm_coe] using hBound index v

/-- The genuine first-jet map on smooth fields, with no new field directions. -/
def llCanonicalSmoothFrameJetLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod) →ₗ[Real]
      LLCanonicalFrameJetL2 period hPeriod :=
  (llH1SmoothToFluxL2LinearMap period hPeriod (analysis.llH1Data period hPeriod)).prod
    (LinearMap.pi fun index => llSmoothCanonicalDerivativeLinearMap period hPeriod analysis index)

/-- Bounded first-jet realization of the positive LL energy completion. -/
def canonicalLLH1FrameJet
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CanonicalLLEnergy period hPeriod analysis →L[Real] LLCanonicalFrameJetL2 period hPeriod :=
  (canonicalLLH1ToFluxL2 period hPeriod analysis).prod
    (ContinuousLinearMap.pi fun index => canonicalLLH1FrameDerivative period hPeriod analysis index)

theorem canonicalLLH1FrameJet_agrees_on_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    canonicalLLH1FrameJet period hPeriod analysis
        (llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod) u) =
      llCanonicalSmoothFrameJetLinearMap period hPeriod analysis u := by
  apply Prod.ext
  · exact canonicalLLH1ToFluxL2_agrees_on_smooth period hPeriod analysis u
  · funext index
    exact canonicalLLH1FrameDerivative_agrees_on_smooth period hPeriod analysis index u

theorem canonicalLLH1FrameJet_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective (canonicalLLH1FrameJet period hPeriod analysis) := by
  intro u v h
  exact canonicalLLH1ToFluxL2_injective period hPeriod analysis (congrArg Prod.fst h)

/-- Closure of the actual smooth value-and-first-derivative graph, not D(C). -/
def canonicalLLFrameH1Graph
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Submodule Real (LLCanonicalFrameJetL2 period hPeriod) :=
  (llCanonicalSmoothFrameJetLinearMap period hPeriod analysis).range.topologicalClosure

/-- Every energy vector has jointly compatible value and derivative coordinates. -/
theorem canonicalLLH1FrameJet_mem_graph
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (u : CanonicalLLEnergy period hPeriod analysis) :
    canonicalLLH1FrameJet period hPeriod analysis u ∈ canonicalLLFrameH1Graph period hPeriod analysis := by
  let e := llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod)
  let J := canonicalLLH1FrameJet period hPeriod analysis
  let S := llCanonicalSmoothFrameJetLinearMap period hPeriod analysis
  have hSubset : Set.range e ⊆ J ⁻¹' closure (Set.range S) := by
    rintro _ ⟨w, rfl⟩
    change J (e w) ∈ closure (Set.range S)
    have hAgreement : J (e w) = S w :=
      canonicalLLH1FrameJet_agrees_on_smooth period hPeriod analysis w
    rw [hAgreement]
    exact subset_closure (Set.mem_range_self w)
  have hClosed : IsClosed (J ⁻¹' closure (Set.range S)) :=
    isClosed_closure.preimage J.continuous
  have hu : u ∈ closure (Set.range e) :=
    llH1SmoothEmbedding_denseRange period hPeriod (analysis.llH1Data period hPeriod) u
  exact (closure_minimal hSubset hClosed) hu

/-- Simultaneous smooth approximation in every first-jet L2 coordinate, with
an energy-norm bound. This is not approximation in the Jacobi graph norm. -/
theorem canonicalLLH1FrameJet_smoothApprox
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (u : CanonicalLLEnergy period hPeriod analysis)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    ∃ w : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod),
      ‖w‖ ≤ ‖u‖ + 1 ∧
      ‖llCanonicalSmoothFrameJetLinearMap period hPeriod analysis w -
        canonicalLLH1FrameJet period hPeriod analysis u‖ < epsilon := by
  let e := llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod)
  let J := canonicalLLH1FrameJet period hPeriod analysis
  let delta : Real := min 1 (epsilon / (‖J‖ + 1))
  have hDen : 0 < ‖J‖ + 1 := by positivity
  have hDelta : 0 < delta := lt_min zero_lt_one (div_pos hEpsilon hDen)
  have hDense : u ∈ closure (Set.range e) :=
    llH1SmoothEmbedding_denseRange period hPeriod (analysis.llH1Data period hPeriod) u
  obtain ⟨y, ⟨w, rfl⟩, hNear⟩ := Metric.mem_closure_iff.mp hDense delta hDelta
  have hApprox : ‖e w - u‖ < delta := by
    simpa only [dist_eq_norm, norm_sub_rev] using hNear
  have hDeltaOne : delta ≤ 1 := min_le_left _ _
  have hNorm : ‖e w‖ = ‖w‖ := by
    change ‖(w : LLH1Space period hPeriod (analysis.llH1Data period hPeriod))‖ = ‖w‖
    exact UniformSpace.Completion.norm_coe w
  have hTriangle := norm_add_le (e w - u) u
  rw [sub_add_cancel, hNorm] at hTriangle
  refine ⟨w, by linarith, ?_⟩
  have hScaled : (‖J‖ + 1) * delta ≤ epsilon := by
    have h := (le_div_iff₀ hDen).mp (min_le_right 1 (epsilon / (‖J‖ + 1)))
    simpa only [mul_comm] using h
  have hProduct : ‖J‖ * delta < epsilon := by nlinarith only [hScaled, hDelta]
  have hAgreement : J (e w) = llCanonicalSmoothFrameJetLinearMap period hPeriod analysis w :=
    canonicalLLH1FrameJet_agrees_on_smooth period hPeriod analysis w
  have hDifference : llCanonicalSmoothFrameJetLinearMap period hPeriod analysis w - J u =
      J (e w - u) := by
    rw [map_sub, hAgreement]
  rw [hDifference]
  exact lt_of_le_of_lt
    ((J.le_opNorm _).trans (mul_le_mul_of_nonneg_left hApprox.le (norm_nonneg J))) hProduct

end
end P0EFTJanusProgramPT12LLCanonicalFrameH1Completion4D
end JanusFormal

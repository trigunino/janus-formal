import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

/-!
# Actual frame-H1 and cutoff control by the positive LL energy

The norms in this module use the existing canonical throat volume and the
existing divergence-free generating frame. The positive LL Hessian controls
the unweighted value-plus-frame-derivative integral, and the same integral
for multiplication by any fixed smooth scalar cutoff. No compact embedding,
coordinate Sobolev comparison, or operator-domain regularity is assumed.

This is the norm-control part of the LL Rellich program, not the Rellich
compactness theorem itself.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
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
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLStrongJacobiGarding4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

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

/-- The indices of the actual canonical LL generating family. -/
abbrev LLCanonicalFrameIndex := Fin (canonicalDivergenceFreeLLFrame period hPeriod).count

/-- Unweighted value-plus-first-derivative density on the actual throat. -/
def llCanonicalFrameH1Density (field : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  ‖field point‖ ^ 2 + throatDerivativeEnergy period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) field point

theorem llCanonicalFrameH1Density_continuous (field : LLWeakTestSpace period hPeriod) :
    Continuous (llCanonicalFrameH1Density period hPeriod field) :=
  (field.contMDiff_toFun.continuous.norm.pow 2).add
    (throatDerivativeEnergy_continuous period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) field)

theorem llCanonicalFrameH1Density_nonneg (field : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    0 ≤ llCanonicalFrameH1Density period hPeriod field point := by
  apply add_nonneg (sq_nonneg _)
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The genuine integrated frame-H1 size, before taking a square root. -/
def llCanonicalFrameH1SizeSq (field : LLWeakTestSpace period hPeriod) : Real :=
  ∫ point, llCanonicalFrameH1Density period hPeriod field point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem llCanonicalSmoothL2_norm_sq (field : LLWeakTestSpace period hPeriod) :
    ‖llSmoothToL2 period hPeriod field‖ ^ 2 =
      ∫ point, ‖field point‖ ^ 2
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(smoothThroatField_memLp period hPeriod LLFieldFiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field).coeFn_toLp]
    with point hPoint
  rw [hPoint, real_inner_self_eq_norm_sq]

theorem llCanonicalFrameH1SizeSq_eq (field : LLWeakTestSpace period hPeriod) :
    llCanonicalFrameH1SizeSq period hPeriod field =
      ‖llSmoothToL2 period hPeriod field‖ ^ 2 +
        ∫ point, throatDerivativeEnergy period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) field point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hv : Integrable (fun point => ‖field point‖ ^ 2)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (field.contMDiff_toFun.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (throatDerivativeEnergy period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) field)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (throatDerivativeEnergy_continuous period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) field).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold llCanonicalFrameH1SizeSq llCanonicalFrameH1Density
  rw [integral_add hv hd, llCanonicalSmoothL2_norm_sq]

private theorem strong_self_pairing_eq_energy
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    inner Real (llStrongJacobiToL2 period hPeriod
        (analysis.llH1Data period hPeriod).fields u.toTest)
      (llSmoothToL2 period hPeriod u.toTest) = ‖u‖ ^ 2 := by
  let data := analysis.llH1Data period hPeriod
  let e := llH1SmoothEmbedding period hPeriod data
  have hPair := canonicalLLH1ToFluxL2_strong_pairing period hPeriod analysis u (e u)
  have hValue := canonicalLLH1ToFluxL2_agrees_on_smooth period hPeriod analysis u
  have hSelf : inner Real (e u) (e u) = ‖u‖ ^ 2 := by
    change inner Real (u : LLH1Space period hPeriod data)
      (u : LLH1Space period hPeriod data) = _
    rw [UniformSpace.Completion.inner_coe, real_inner_self_eq_norm_sq]
  have hReplace := congrArg
    (fun value : CanonicalLLL2 period hPeriod analysis =>
      inner Real (llStrongJacobiToL2 period hPeriod data.fields u.toTest) value)
    hValue.symm
  exact Eq.trans hReplace (Eq.trans hPair.symm hSelf)

/-- The actual positive LL energy controls its unweighted frame-H1 size.
The constant depends only on the fixed background, never on the direction. -/
theorem canonicalLLSmooth_frameH1_bound
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ∃ K : Real, 0 < K ∧
      ∀ u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod),
        llCanonicalFrameH1SizeSq period hPeriod u.toTest ≤ K * ‖u‖ ^ 2 := by
  obtain ⟨k, hk, hValue⟩ := canonicalLLH1SmoothToFluxL2_bound period hPeriod analysis
  obtain ⟨c, hc, hGarding⟩ := llStrongJacobi_smooth_l2_garding period hPeriod
    (analysis.llH1Data period hPeriod).fields
  refine ⟨2 + (2 * c + 1) * k ^ 2, by positivity, ?_⟩
  intro u
  have hv : ‖llSmoothToL2 period hPeriod u.toTest‖ ≤ k * ‖u‖ := hValue u
  have hvsq : ‖llSmoothToL2 period hPeriod u.toTest‖ ^ 2 ≤ k ^ 2 * ‖u‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hk (norm_nonneg u))).2 hv
  have hg := hGarding u.toTest
  rw [strong_self_pairing_eq_energy period hPeriod analysis u] at hg
  have hw := mul_le_mul_of_nonneg_left hvsq
    (show 0 ≤ 2 * c + 1 by positivity)
  rw [llCanonicalFrameH1SizeSq_eq]
  nlinarith only [hg, hw]

/-- Multiplication by a genuine smooth scalar cutoff on the same throat. -/
def llSmoothCutoff (cutoff : SmoothThroatField period hPeriod Real)
    (field : LLWeakTestSpace period hPeriod) : LLWeakTestSpace period hPeriod where
  toFun point := cutoff point • field point
  contMDiff_toFun := cutoff.contMDiff_toFun.smul field.contMDiff_toFun

/-- The actual manifold derivative satisfies the cutoff Leibniz rule. -/
theorem llSmoothCutoff_frameDerivative
    (cutoff : SmoothThroatField period hPeriod Real)
    (field : LLWeakTestSpace period hPeriod) (point : EffectiveThroat period hPeriod)
    (index : LLCanonicalFrameIndex period hPeriod) :
    throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (llSmoothCutoff period hPeriod cutoff field) point index =
      cutoff point • throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field point index +
      throatFrameDerivative period hPeriod Real
        (canonicalDivergenceFreeLLFrame period hPeriod) cutoff point index • field point := by
  rw [throatFrameDerivative_eq_mvfderiv, throatFrameDerivative_eq_mvfderiv,
    throatFrameDerivative_eq_mvfderiv]
  change mvfderiv throatCoverModelWithCorners (cutoff.toFun • field.toFun) point
    ((canonicalDivergenceFreeLLFrame period hPeriod).vectorAt point index) = _
  rw [mvfderiv_smul
    ((cutoff.contMDiff_toFun.mdifferentiable (by simp)) point)
    ((field.contMDiff_toFun.mdifferentiable (by simp)) point)]
  rfl

theorem llSmoothCutoff_support_subset
    (cutoff : SmoothThroatField period hPeriod Real)
    (field : LLWeakTestSpace period hPeriod) :
    Function.support (llSmoothCutoff period hPeriod cutoff field).toFun ⊆
      Function.support cutoff.toFun := by
  intro point hPoint hZero
  apply hPoint
  change cutoff point • field point = 0
  rw [hZero, zero_smul]

/-- Localization also preserves the closed support needed by chartwise Rellich. -/
theorem llSmoothCutoff_tsupport_subset
    (cutoff : SmoothThroatField period hPeriod Real)
    (field : LLWeakTestSpace period hPeriod) :
    tsupport (llSmoothCutoff period hPeriod cutoff field).toFun ⊆ tsupport cutoff.toFun := by
  exact closure_mono (llSmoothCutoff_support_subset period hPeriod cutoff field)

private def cutoffFrameEnergy (cutoff : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  ∑ index : LLCanonicalFrameIndex period hPeriod,
    ‖throatFrameDerivative period hPeriod Real
      (canonicalDivergenceFreeLLFrame period hPeriod) cutoff point index‖ ^ 2

private theorem cutoffFrameEnergy_continuous
    (cutoff : SmoothThroatField period hPeriod Real) :
    Continuous (cutoffFrameEnergy period hPeriod cutoff) := by
  apply continuous_finsetSum
  intro index _
  exact (((continuous_apply index).comp
    (throatFrameDerivative_contMDiff period hPeriod Real
      (canonicalDivergenceFreeLLFrame period hPeriod) cutoff).continuous).norm.pow 2)

private theorem cutoff_derivative_energy_le
    (cutoff : SmoothThroatField period hPeriod Real)
    (field : LLWeakTestSpace period hPeriod) (point : EffectiveThroat period hPeriod) :
    throatDerivativeEnergy period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (llSmoothCutoff period hPeriod cutoff field) point ≤
      2 * ‖cutoff point‖ ^ 2 * throatDerivativeEnergy period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) field point +
      2 * cutoffFrameEnergy period hPeriod cutoff point * ‖field point‖ ^ 2 := by
  have hOne (index : LLCanonicalFrameIndex period hPeriod) :
      ‖throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (llSmoothCutoff period hPeriod cutoff field) point index‖ ^ 2 ≤
      2 * ‖cutoff point‖ ^ 2 *
        ‖throatFrameDerivative period hPeriod LLFieldFiber
          (canonicalDivergenceFreeLLFrame period hPeriod) field point index‖ ^ 2 +
      2 * ‖throatFrameDerivative period hPeriod Real
        (canonicalDivergenceFreeLLFrame period hPeriod) cutoff point index‖ ^ 2 *
          ‖field point‖ ^ 2 := by
    rw [llSmoothCutoff_frameDerivative]
    have hTwo (a b : LLFieldFiber) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      rw [norm_add_sq_real]
      nlinarith [real_inner_le_norm a b, sq_nonneg (‖a‖ - ‖b‖)]
    simpa only [norm_smul, mul_pow, mul_assoc] using hTwo
      (cutoff point • throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field point index)
      (throatFrameDerivative period hPeriod Real
        (canonicalDivergenceFreeLLFrame period hPeriod) cutoff point index • field point)
  have hSum := Finset.sum_le_sum (fun index (_ : index ∈ Finset.univ) => hOne index)
  simpa only [throatDerivativeEnergy, cutoffFrameEnergy,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc] using hSum

/-- Every fixed smooth cutoff is bounded for the actual unweighted frame-H1 size.
The coefficient bound is obtained from compactness of the throat itself. -/
theorem llSmoothCutoff_frameH1_bound
    (cutoff : SmoothThroatField period hPeriod Real) :
    ∃ B : Real, 0 < B ∧ ∀ field : LLWeakTestSpace period hPeriod,
      llCanonicalFrameH1SizeSq period hPeriod (llSmoothCutoff period hPeriod cutoff field) ≤
        B * llCanonicalFrameH1SizeSq period hPeriod field := by
  have hCont : Continuous (fun point => ‖cutoff point‖ ^ 2 +
      cutoffFrameEnergy period hPeriod cutoff point) :=
    (cutoff.contMDiff_toFun.continuous.norm.pow 2).add
      (cutoffFrameEnergy_continuous period hPeriod cutoff)
  obtain ⟨b, hb⟩ := isCompact_univ.exists_bound_of_continuousOn hCont.continuousOn
  let M : Real := max b 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  have hBounds (point : EffectiveThroat period hPeriod) :
      ‖cutoff point‖ ^ 2 ≤ M ∧ cutoffFrameEnergy period hPeriod cutoff point ≤ M := by
    have hNonneg : 0 ≤ cutoffFrameEnergy period hPeriod cutoff point :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h := hb point (Set.mem_univ point)
    have hAbs : |‖cutoff point‖ ^ 2 + cutoffFrameEnergy period hPeriod cutoff point| ≤ b := by
      simpa only [Real.norm_eq_abs] using h
    have hTotal : ‖cutoff point‖ ^ 2 + cutoffFrameEnergy period hPeriod cutoff point ≤ M :=
      (le_abs_self _).trans (hAbs.trans (le_max_left b 1))
    constructor <;> linarith [sq_nonneg ‖cutoff point‖]
  refine ⟨3 * M, by positivity, ?_⟩
  intro field
  have hPoint (point : EffectiveThroat period hPeriod) :
      llCanonicalFrameH1Density period hPeriod (llSmoothCutoff period hPeriod cutoff field) point ≤
        (3 * M) * llCanonicalFrameH1Density period hPeriod field point := by
    have hg := cutoff_derivative_energy_le period hPeriod cutoff field point
    have hEnergy : 0 ≤ throatDerivativeEnergy period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) field point :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hv := mul_le_mul_of_nonneg_right (hBounds point).1 (sq_nonneg ‖field point‖)
    have hd := mul_le_mul_of_nonneg_right (hBounds point).1 hEnergy
    have hc := mul_le_mul_of_nonneg_right (hBounds point).2 (sq_nonneg ‖field point‖)
    have hm := mul_nonneg hM.le hEnergy
    change ‖cutoff point • field point‖ ^ 2 + _ ≤ _
    rw [norm_smul, mul_pow]
    unfold llCanonicalFrameH1Density
    nlinarith only [hg, hv, hd, hc, hm]
  have hLeft : Integrable (llCanonicalFrameH1Density period hPeriod
      (llSmoothCutoff period hPeriod cutoff field))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (llCanonicalFrameH1Density_continuous period hPeriod
      (llSmoothCutoff period hPeriod cutoff field)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRight : Integrable (llCanonicalFrameH1Density period hPeriod field)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (llCanonicalFrameH1Density_continuous period hPeriod field).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral := integral_mono hLeft (hRight.const_mul (3 * M)) hPoint
  rw [integral_const_mul] at hIntegral
  exact hIntegral

/-- Actual LL-energy control of localized values and all canonical derivatives.
This discharges a concrete norm estimate needed by chartwise Rellich, not
chartwise compactness or equivalence with a Euclidean Sobolev norm. -/
theorem canonicalLLSmooth_cutoff_frameH1_bound
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (cutoff : SmoothThroatField period hPeriod Real) :
    ∃ K : Real, 0 < K ∧
      ∀ u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod),
        llCanonicalFrameH1SizeSq period hPeriod
          (llSmoothCutoff period hPeriod cutoff u.toTest) ≤ K * ‖u‖ ^ 2 := by
  obtain ⟨A, hA, hEnergy⟩ := canonicalLLSmooth_frameH1_bound period hPeriod analysis
  obtain ⟨B, hB, hCutoff⟩ := llSmoothCutoff_frameH1_bound period hPeriod cutoff
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro u
  have h := (hCutoff u.toTest).trans (mul_le_mul_of_nonneg_left (hEnergy u) hB.le)
  simpa only [mul_assoc] using h

end
end P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiPositiveCoercivity4D
import Mathlib.Analysis.Normed.Operator.Extend

/-! The positive canonical LL Hessian controls the L² value of a smooth field. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiPositiveCoercivity4D

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

/-- The canonical positive LL energy norm bounds its genuine throat L² value. -/
theorem canonicalLLH1SmoothToFluxL2_bound
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ∃ K : Real, 0 ≤ K ∧
      ∀ u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod),
        ‖llH1SmoothToFluxL2 period hPeriod
            (analysis.llH1Data period hPeriod) u‖ ≤ K * ‖u‖ := by
  let data := analysis.llH1Data period hPeriod
  obtain ⟨c, hc, hLower⟩ :=
    llStrongJacobi_smooth_positive_l2_lower_bound period hPeriod
      data.fields data.llMeasure_pos
  have hEnergy (u : LLH1Smooth period hPeriod data) :
      c * ‖llH1SmoothToFluxL2 period hPeriod data u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have hAE :
        (llSmoothToL2 period hPeriod u.toTest :
          EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
            intrinsicCanonicalThroatVolumeMeasure period hPeriod] u.toTest.toFun :=
      (smoothThroatField_memLp period hPeriod LLFieldFiber
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) u.toTest).coeFn_toLp
    have hPairing :
        inner Real (llStrongJacobiToL2 period hPeriod data.fields u.toTest)
            (llSmoothToL2 period hPeriod u.toTest) =
          globalPTSymmetricDifferentialLLFluxHessian period hPeriod
            data.frame data.fields u.toTest u.toTest data.mu := by
      rw [L2.inner_def]
      calc
        (∫ point,
          inner Real (llStrongJacobiToL2 period hPeriod data.fields u.toTest point)
            (llSmoothToL2 period hPeriod u.toTest point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
            ∫ point,
              inner Real (llStrongJacobiToL2 period hPeriod data.fields u.toTest point)
                (u.toTest point)
              ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
                apply integral_congr_ae
                filter_upwards [hAE] with point hPoint
                rw [hPoint]
        _ = _ := by
          simpa only [data, GlobalAnalysisData.llH1Data] using
            (llStrongJacobiToL2_pairing_eq_hessian period hPeriod
              data.fields u.toTest u.toTest)
    have hValue :
        llH1SmoothToFluxL2 period hPeriod data u =
          llSmoothToL2 period hPeriod u.toTest := by
      rfl
    have h := hLower u.toTest
    rw [hPairing, ← llH1Smooth_inner period hPeriod data u u,
      real_inner_self_eq_norm_sq] at h
    exact h
  let K := Real.sqrt c⁻¹
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  refine ⟨K, hK, ?_⟩
  intro u
  have hBound := hEnergy u
  have hSquare :
      ‖llH1SmoothToFluxL2 period hPeriod data u‖ ^ 2 ≤
        (K * ‖u‖) ^ 2 := by
    calc
      ‖llH1SmoothToFluxL2 period hPeriod data u‖ ^ 2 ≤
          c⁻¹ * ‖u‖ ^ 2 := by
            calc
              _ = c⁻¹ * (c * ‖llH1SmoothToFluxL2 period hPeriod data u‖ ^ 2) := by
                rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
              _ ≤ c⁻¹ * ‖u‖ ^ 2 :=
                mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr hc.le)
      _ = (K * ‖u‖) ^ 2 := by
        rw [mul_pow, show K ^ 2 = c⁻¹ from Real.sq_sqrt (inv_nonneg.mpr hc.le)]
  have hResult :
      ‖llH1SmoothToFluxL2 period hPeriod data u‖ ≤ K * ‖u‖ := by
    nlinarith [norm_nonneg (llH1SmoothToFluxL2 period hPeriod data u),
      mul_nonneg hK (norm_nonneg u)]
  exact hResult

/-- Continuous L² value map from the canonical positive LL energy completion. -/
def canonicalLLH1ToFluxL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    LLH1Space period hPeriod (analysis.llH1Data period hPeriod) →L[Real]
      LLFluxL2 period hPeriod (analysis.llH1Data period hPeriod) :=
  LinearMap.extendOfNorm
    (llH1SmoothToFluxL2LinearMap period hPeriod
      (analysis.llH1Data period hPeriod))
    (llH1SmoothEmbedding period hPeriod
      (analysis.llH1Data period hPeriod))

theorem canonicalLLH1ToFluxL2_agrees_on_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    canonicalLLH1ToFluxL2 period hPeriod analysis
        (llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) u) =
      llH1SmoothToFluxL2 period hPeriod
        (analysis.llH1Data period hPeriod) u := by
  apply LinearMap.extendOfNorm_eq
  · exact llH1SmoothEmbedding_denseRange period hPeriod
      (analysis.llH1Data period hPeriod)
  · obtain ⟨K, _, hK⟩ :=
      canonicalLLH1SmoothToFluxL2_bound period hPeriod analysis
    refine ⟨K, ?_⟩
    intro u
    change ‖llH1SmoothToFluxL2 period hPeriod
        (analysis.llH1Data period hPeriod) u‖ ≤
      K * ‖(u : LLH1Space period hPeriod
        (analysis.llH1Data period hPeriod))‖
    simpa only [UniformSpace.Completion.norm_coe] using hK u

end
end P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
end JanusFormal

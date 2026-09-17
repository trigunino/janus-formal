import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

/-! The canonical positive LL energy completion embeds faithfully into throat L². -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D

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
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

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

/-- The canonical LL energy completion has no nonzero vector with zero L² value. -/
theorem canonicalLLH1ToFluxL2_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective (canonicalLLH1ToFluxL2 period hPeriod analysis) := by
  let data := analysis.llH1Data period hPeriod
  let e := llH1SmoothEmbedding period hPeriod data
  let I := canonicalLLH1ToFluxL2 period hPeriod analysis
  have hCore (v u : LLH1Smooth period hPeriod data) :
      weakLLJacobiH1Extension period hPeriod data v (e u) =
        inner Real
          (llStrongJacobiToL2 period hPeriod data.fields v.toTest)
          (llH1SmoothToFluxL2 period hPeriod data u) := by
    rw [weakLLJacobiH1Extension_apply_smooth]
    rw [L2.inner_def]
    calc
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          data.frame data.fields v.toTest u.toTest data.mu =
        ∫ point, inner Real
          (llStrongJacobiToL2 period hPeriod data.fields v.toTest point)
          (u.toTest point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
            simpa only [data, GlobalAnalysisData.llH1Data] using
              (llStrongJacobiToL2_pairing_eq_hessian period hPeriod
                data.fields v.toTest u.toTest).symm
      _ = ∫ point, inner Real
          (llStrongJacobiToL2 period hPeriod data.fields v.toTest point)
          (llH1SmoothToFluxL2 period hPeriod data u point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
            apply integral_congr_ae
            filter_upwards [llH1SmoothToFluxL2_ae period hPeriod data u]
              with point hPoint
            rw [hPoint]
  have hPairing (v : LLH1Smooth period hPeriod data)
      (x : LLH1Space period hPeriod data) :
      weakLLJacobiH1Extension period hPeriod data v x =
        inner Real (llStrongJacobiToL2 period hPeriod data.fields v.toTest) (I x) := by
    have hEq := (llH1SmoothEmbedding_denseRange period hPeriod data).equalizer
      (weakLLJacobiH1Extension period hPeriod data v).continuous
      (continuous_const.inner I.continuous)
      (by
        funext u
        change weakLLJacobiH1Extension period hPeriod data v (e u) =
          inner Real (llStrongJacobiToL2 period hPeriod data.fields v.toTest)
            (I (e u))
        rw [canonicalLLH1ToFluxL2_agrees_on_smooth]
        exact hCore v u)
    exact congrFun hEq x
  intro x y hxy
  apply sub_eq_zero.mp
  refine (llH1SmoothEmbedding_denseRange period hPeriod data).eq_zero_of_inner_right
    (𝕜 := Real) ?_
  intro v
  have hVanishing := hPairing v (x - y)
  change inner Real (e v) (x - y) = _ at hVanishing
  rw [map_sub, hxy, sub_self] at hVanishing
  have hZeroInner : inner Real
      (llStrongJacobiToL2 period hPeriod data.fields v.toTest)
      (0 : LLFluxL2 period hPeriod data) = 0 := by
    change inner Real
      (llStrongJacobiToL2 period hPeriod data.fields v.toTest)
      (0 : Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = 0
    exact inner_zero_right
      (llStrongJacobiToL2 period hPeriod data.fields v.toTest)
  exact hVanishing.trans hZeroInner

end
end P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D
end JanusFormal

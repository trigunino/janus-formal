import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFiniteFiberCompactness4D

/-!
# Smooth Rellich transport on canonical LL throat patches

Euclidean patch values return continuously to scalar throat `L²`, and the
finite partition reconstructs each smooth LL coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichTransport4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLCanonicalFiniteFiberCompactness4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchVolumeComparison4D
open P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchLpTransport4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothLocalization4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichLocalBound4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichExtension4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev Patch :=
  FiniteThroatGeneratorPatch period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatVolumeIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalThroatChartHilbertCoordinates :=
  borel CanonicalThroatChartHilbertCoordinates

local instance canonicalThroatChartHilbertBorelSpace :
    BorelSpace CanonicalThroatChartHilbertCoordinates where
  measurable_eq := rfl

/-- Pointwise representative of the public scalar-coordinate projection. -/
theorem llFluxL2Coordinate_coeFn_ae_eq
    (data : PositiveLLH1Data period hPeriod)
    (component : Fin 4)
    (field : LLFluxL2 period hPeriod data) :
    (llFluxL2Coordinate period hPeriod data component field :
      EffectiveThroat period hPeriod → Real) =ᵐ[data.mu]
        fun point => field point component := by
  have hCoordinateMap :
      llFluxL2Coordinate period hPeriod data component =
        (llFieldComponentProjection component).compLpL
          (2 : ENNReal) data.mu :=
    rfl
  rw [hCoordinateMap]
  simpa only [llFieldComponentProjection_apply] using
    (llFieldComponentProjection component).coeFn_compLpL field

/-- Return from one Euclidean patch `L²` space to one scalar coordinate of
the canonical throat `L²` space. -/
def finiteThroatGeneratorPatchEuclideanL2ToLLScalarL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod) :
    FiniteThroatGeneratorPatchEuclideanL2 →L[Real]
      LLScalarL2 period hPeriod (analysis.llH1Data period hPeriod) :=
  (finiteThroatGeneratorPatchSourceToQuotientL2
    period hPeriod patch).comp
    (finiteThroatGeneratorPatchAmbientToSourceLp
      (Fiber := Real) period hPeriod patch
      (finiteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch))

theorem finiteThroatGeneratorPatchEuclideanRellichEmbedding_localized
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchEuclideanRellichEmbedding
        period hPeriod patch
        (finiteThroatGeneratorPatchSmoothEuclideanH1
          period hPeriod patch component field) =
      finiteThroatGeneratorPatchLocalizedValueL2
        period hPeriod patch component field :=
  rfl

theorem finiteThroatGeneratorPatchEuclideanL2ToLLScalarL2_localized
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchEuclideanL2ToLLScalarL2
        period hPeriod analysis patch
        (finiteThroatGeneratorPatchEuclideanRellichEmbedding
          period hPeriod patch
          (finiteThroatGeneratorPatchSmoothEuclideanH1
            period hPeriod patch component field)) =
      finiteThroatGeneratorPatchCutComponentL2
        period hPeriod patch component field := by
  rw [finiteThroatGeneratorPatchEuclideanRellichEmbedding_localized
    period hPeriod patch component field]
  exact
    finiteThroatGeneratorPatchLocalizedValueExtension_eq
      period hPeriod patch
      (finiteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) component field

/-- The partition-localized scalar components reconstruct one coordinate of
the smooth LL `L²` field. -/
theorem finiteThroatGeneratorPatchCutComponentL2_sum_eq_coordinate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (component : Fin 4)
    (u : LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod)) :
    (∑ patch : Patch period hPeriod,
      finiteThroatGeneratorPatchCutComponentL2
        period hPeriod patch component u.toTest) =
      llFluxL2Coordinate period hPeriod
        (analysis.llH1Data period hPeriod) component
        (llH1SmoothToFluxL2 period hPeriod
          (analysis.llH1Data period hPeriod) u) := by
  apply Lp.ext
  letI := intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  have hSum :=
    Lp.coeFn_fun_finsetSum
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (Finset.univ : Finset (Patch period hPeriod))
      (fun patch =>
        finiteThroatGeneratorPatchCutComponentL2
          period hPeriod patch component u.toTest)
  have hWeighted :
      ∀ᵐ point ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod,
        ∀ patch : Patch period hPeriod,
          finiteThroatGeneratorPatchCutComponentL2
              period hPeriod patch component u.toTest point =
            finiteThroatGeneratorWeight period hPeriod patch point *
              u.toTest point component :=
    ae_all_iff.2 fun patch => by
      filter_upwards
        [finiteThroatGeneratorPatchCutComponentL2_coeFn_ae_eq
          period hPeriod patch component u.toTest]
        with point hPoint
      rw [hPoint,
        finiteThroatGeneratorPatchCutComponent_apply]
  have hProjected :
      (llFluxL2Coordinate period hPeriod
          (analysis.llH1Data period hPeriod) component
          (llH1SmoothToFluxL2 period hPeriod
            (analysis.llH1Data period hPeriod) u) :
        EffectiveThroat period hPeriod → Real) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        fun point =>
          llH1SmoothToFluxL2 period hPeriod
            (analysis.llH1Data period hPeriod) u point component := by
    simpa only [GlobalAnalysisData.llH1Data] using
      llFluxL2Coordinate_coeFn_ae_eq period hPeriod
        (analysis.llH1Data period hPeriod) component
        (llH1SmoothToFluxL2 period hPeriod
          (analysis.llH1Data period hPeriod) u)
  have hSmooth :
      (llH1SmoothToFluxL2 period hPeriod
          (analysis.llH1Data period hPeriod) u :
        EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        u.toTest.toFun := by
    simpa only [GlobalAnalysisData.llH1Data] using
      llH1SmoothToFluxL2_ae period hPeriod
        (analysis.llH1Data period hPeriod) u
  have hOriginal :
      (llFluxL2Coordinate period hPeriod
          (analysis.llH1Data period hPeriod) component
          (llH1SmoothToFluxL2 period hPeriod
            (analysis.llH1Data period hPeriod) u) :
        EffectiveThroat period hPeriod → Real) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        fun point => u.toTest point component := by
    filter_upwards [hProjected, hSmooth]
      with point hProjected hSmooth
    rw [hProjected, hSmooth]
  filter_upwards [hSum, hWeighted, hOriginal]
    with point hSum hWeighted hOriginal
  rw [hSum]
  calc
    _ = u.toTest point component := by
      simp_rw [hWeighted]
      rw [← Finset.sum_mul,
        finiteThroatGeneratorWeight_sum_eq_one, one_mul]
    _ = _ := hOriginal.symm

end
end P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichTransport4D
end JanusFormal

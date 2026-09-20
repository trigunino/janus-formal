import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichTransport4D

/-!
# Canonical LL throat Rellich compactness

Finite throat-patch Rellich contributions reconstruct every scalar LL
coordinate, hence the completed vector-valued LL embedding is compact.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatRellichCompactness4D

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
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalFiniteFiberCompactness4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichLocalBound4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichExtension4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichTransport4D

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

/-- One completed scalar contribution from a genuine throat patch. -/
def finiteThroatGeneratorPatchRellichContribution
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4) :
    CanonicalLLEnergy period hPeriod analysis →L[Real]
      LLScalarL2 period hPeriod (analysis.llH1Data period hPeriod) :=
  (finiteThroatGeneratorPatchEuclideanL2ToLLScalarL2
    period hPeriod analysis patch).comp
    ((finiteThroatGeneratorPatchEuclideanRellichEmbedding
      period hPeriod patch).comp
      (finiteThroatGeneratorPatchEuclideanH1Localizer
        period hPeriod analysis patch component))

theorem finiteThroatGeneratorPatchRellichContribution_agrees_on_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (u : LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod)) :
    finiteThroatGeneratorPatchRellichContribution
        period hPeriod analysis patch component
        (llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) u) =
      finiteThroatGeneratorPatchCutComponentL2
        period hPeriod patch component u.toTest := by
  simp only [finiteThroatGeneratorPatchRellichContribution,
    ContinuousLinearMap.comp_apply]
  rw [finiteThroatGeneratorPatchEuclideanH1Localizer_agrees_on_smooth
    period hPeriod analysis patch component u]
  exact
    finiteThroatGeneratorPatchEuclideanL2ToLLScalarL2_localized
      period hPeriod analysis patch component u.toTest

theorem finiteThroatGeneratorPatchRellichContribution_isCompact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4) :
    IsCompactOperator
      (finiteThroatGeneratorPatchRellichContribution
        period hPeriod analysis patch component) := by
  change IsCompactOperator
    ((finiteThroatGeneratorPatchEuclideanL2ToLLScalarL2
        period hPeriod analysis patch).comp
      ((finiteThroatGeneratorPatchEuclideanRellichEmbedding
        period hPeriod patch).comp
        (finiteThroatGeneratorPatchEuclideanH1Localizer
          period hPeriod analysis patch component)))
  exact
    ((finiteThroatGeneratorPatchEuclideanRellichEmbedding_isCompact
        period hPeriod patch).comp_clm
      (finiteThroatGeneratorPatchEuclideanH1Localizer
        period hPeriod analysis patch component)).clm_comp
      (finiteThroatGeneratorPatchEuclideanL2ToLLScalarL2
        period hPeriod analysis patch)

/-- Each completed scalar coordinate factors through the finite sum of its
compact patch contributions. -/
theorem canonicalLLH1Coordinate_factorization
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (component : Fin 4) :
    (llFluxL2Coordinate period hPeriod
        (analysis.llH1Data period hPeriod) component).comp
        (canonicalLLH1ToFluxL2 period hPeriod analysis) =
      ∑ patch : Patch period hPeriod,
        finiteThroatGeneratorPatchRellichContribution
          period hPeriod analysis patch component := by
  classical
  let lhs :=
    (llFluxL2Coordinate period hPeriod
      (analysis.llH1Data period hPeriod) component).comp
      (canonicalLLH1ToFluxL2 period hPeriod analysis)
  let rhs :=
    ∑ patch : Patch period hPeriod,
      finiteThroatGeneratorPatchRellichContribution
        period hPeriod analysis patch component
  have hFunctions : (fun field => lhs field) = fun field => rhs field :=
    (llH1SmoothEmbedding_denseRange period hPeriod
      (analysis.llH1Data period hPeriod)).equalizer
        lhs.continuous rhs.continuous (by
          funext u
          simp only [Function.comp_apply]
          dsimp only [lhs, rhs]
          simp only [ContinuousLinearMap.comp_apply, sum_apply]
          change
            llFluxL2Coordinate period hPeriod
                (analysis.llH1Data period hPeriod) component
                (canonicalLLH1ToFluxL2 period hPeriod analysis
                  (llH1SmoothEmbedding period hPeriod
                    (analysis.llH1Data period hPeriod) u)) =
              ∑ patch : Patch period hPeriod,
                finiteThroatGeneratorPatchRellichContribution
                  period hPeriod analysis patch component
                  (llH1SmoothEmbedding period hPeriod
                    (analysis.llH1Data period hPeriod) u)
          rw [canonicalLLH1ToFluxL2_agrees_on_smooth]
          simp_rw [
            finiteThroatGeneratorPatchRellichContribution_agrees_on_smooth]
          convert
            (finiteThroatGeneratorPatchCutComponentL2_sum_eq_coordinate
              period hPeriod analysis component u).symm using 1 <;>
            rfl)
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.ext
  intro field
  exact congrFun hFunctions field

theorem canonicalLLH1Coordinate_isCompact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (component : Fin 4) :
    IsCompactOperator
      ((llFluxL2Coordinate period hPeriod
          (analysis.llH1Data period hPeriod) component).comp
        (canonicalLLH1ToFluxL2 period hPeriod analysis)) := by
  classical
  rw [canonicalLLH1Coordinate_factorization
    period hPeriod analysis component]
  change
    (∑ patch : Patch period hPeriod,
      finiteThroatGeneratorPatchRellichContribution
        period hPeriod analysis patch component) ∈
      compactOperator (RingHom.id Real)
        (CanonicalLLEnergy period hPeriod analysis)
        (LLScalarL2 period hPeriod
          (analysis.llH1Data period hPeriod))
  exact Submodule.sum_mem _ fun patch _ =>
    finiteThroatGeneratorPatchRellichContribution_isCompact
      period hPeriod analysis patch component

/-- Rellich compactness of the canonical completed LL value embedding. -/
theorem canonicalLLH1ToFluxL2_isCompact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsCompactOperator
      (canonicalLLH1ToFluxL2 period hPeriod analysis) :=
  (canonicalLLH1ToFluxL2_isCompact_iff_coordinate
    period hPeriod analysis).2 fun component =>
      canonicalLLH1Coordinate_isCompact
        period hPeriod analysis component

end
end P0EFTJanusProgramPT12LLCanonicalThroatRellichCompactness4D
end JanusFormal

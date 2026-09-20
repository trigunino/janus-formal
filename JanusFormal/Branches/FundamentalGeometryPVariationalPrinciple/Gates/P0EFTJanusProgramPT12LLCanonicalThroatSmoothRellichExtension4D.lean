import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichLocalBound4D

/-!
# Completed smooth localizers on canonical LL throat patches

The scalar smooth patch localizer is linear and extends continuously from the
dense smooth LL core to the completed canonical LL energy space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichExtension4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalThroatChartDifferential4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothLocalization4D
open P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichLocalBound4D

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

local instance canonicalThroatChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalThroatChartHilbertCoordinates :=
  borel CanonicalThroatChartHilbertCoordinates

local instance canonicalThroatChartHilbertBorelSpace :
    BorelSpace CanonicalThroatChartHilbertCoordinates where
  measurable_eq := rfl

theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_add
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (first second : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchLocalizedCoordinateFunction
        period hPeriod patch component (first + second) =
      finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component first +
        finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component second := by
  funext coordinate
  by_cases hCoordinate :
      coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch
  · simp only [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
      Set.indicator_of_mem hCoordinate, Pi.add_apply]
    change
      finiteThroatGeneratorWeight period hPeriod patch
          (finiteThroatGeneratorPatchHilbertInverse
            period hPeriod patch coordinate) *
          (first (finiteThroatGeneratorPatchHilbertInverse
                period hPeriod patch coordinate) component +
            second (finiteThroatGeneratorPatchHilbertInverse
                period hPeriod patch coordinate) component) =
        _
    rw [finiteThroatGeneratorPatchCutComponent_apply,
      finiteThroatGeneratorPatchCutComponent_apply]
    ring
  · simp [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
      Set.indicator_of_notMem hCoordinate]

theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_smul
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (scalar : Real)
    (field : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchLocalizedCoordinateFunction
        period hPeriod patch component (scalar • field) =
      scalar •
        finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field := by
  funext coordinate
  by_cases hCoordinate :
      coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch
  · simp only [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
      Set.indicator_of_mem hCoordinate, Pi.smul_apply]
    rw [finiteThroatGeneratorPatchCutComponent_apply]
    change
      finiteThroatGeneratorWeight period hPeriod patch
          (finiteThroatGeneratorPatchHilbertInverse
            period hPeriod patch coordinate) *
          (scalar * field
            (finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch coordinate) component) =
        scalar *
          (finiteThroatGeneratorWeight period hPeriod patch
              (finiteThroatGeneratorPatchHilbertInverse
                period hPeriod patch coordinate) *
            field (finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch coordinate) component)
    ring
  · simp [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
      Set.indicator_of_notMem hCoordinate]

theorem finiteThroatGeneratorPatchLocalizedC1c_add
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (first second : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchLocalizedC1c
        period hPeriod patch component (first + second) =
      finiteThroatGeneratorPatchLocalizedC1c
          period hPeriod patch component first +
        finiteThroatGeneratorPatchLocalizedC1c
          period hPeriod patch component second :=
  Subtype.ext
    (finiteThroatGeneratorPatchLocalizedCoordinateFunction_add
      period hPeriod patch component first second)

theorem finiteThroatGeneratorPatchLocalizedC1c_smul
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (scalar : Real)
    (field : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchLocalizedC1c
        period hPeriod patch component (scalar • field) =
      scalar •
        finiteThroatGeneratorPatchLocalizedC1c
          period hPeriod patch component field :=
  Subtype.ext
    (finiteThroatGeneratorPatchLocalizedCoordinateFunction_smul
      period hPeriod patch component scalar field)

/-- Linear smooth-core localizer on one scalar component of one throat patch. -/
def finiteThroatGeneratorPatchSmoothEuclideanH1LinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4) :
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod) →ₗ[Real]
      FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch where
  toFun u :=
    finiteThroatGeneratorPatchSmoothEuclideanH1
      period hPeriod patch component u.toTest
  map_add' first second := by
    apply Subtype.ext
    apply Subtype.ext
    change
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
          (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
          (E := CanonicalThroatChartHilbertCoordinates)
          (finiteThroatGeneratorPatchLocalizedC1c
            period hPeriod patch component (first + second).toTest) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
            (E := CanonicalThroatChartHilbertCoordinates)
            (finiteThroatGeneratorPatchLocalizedC1c
              period hPeriod patch component first.toTest) +
          RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
            (E := CanonicalThroatChartHilbertCoordinates)
            (finiteThroatGeneratorPatchLocalizedC1c
              period hPeriod patch component second.toTest)
    rw [LLH1Smooth.toTest_add,
      finiteThroatGeneratorPatchLocalizedC1c_add]
    exact
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
        (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
        (E := CanonicalThroatChartHilbertCoordinates)).map_add _ _
  map_smul' scalar field := by
    apply Subtype.ext
    apply Subtype.ext
    change
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
          (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
          (E := CanonicalThroatChartHilbertCoordinates)
          (finiteThroatGeneratorPatchLocalizedC1c
            period hPeriod patch component (scalar • field).toTest) =
        scalar •
          RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
            (E := CanonicalThroatChartHilbertCoordinates)
            (finiteThroatGeneratorPatchLocalizedC1c
              period hPeriod patch component field.toTest)
    rw [LLH1Smooth.toTest_smul,
      finiteThroatGeneratorPatchLocalizedC1c_smul]
    exact
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
        (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
        (E := CanonicalThroatChartHilbertCoordinates)).map_smul scalar _

/-- Continuous extension of one scalar patch localizer to completed LL energy. -/
def finiteThroatGeneratorPatchEuclideanH1Localizer
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4) :
    CanonicalLLEnergy period hPeriod analysis →L[Real]
      FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch := by
  letI : IsBoundedSMul Real
      (FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch) :=
    @NormedSpace.toIsBoundedSMul
      Real (FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch)
      inferInstance inferInstance inferInstance
  exact LinearMap.extendOfNorm
    (𝕜 := Real) (𝕜₂ := Real)
    (E := LLH1Smooth period hPeriod
      (analysis.llH1Data period hPeriod))
    (Eₗ := CanonicalLLEnergy period hPeriod analysis)
    (F := FiniteThroatGeneratorPatchEuclideanH1
      period hPeriod patch)
    (σ₁₂ := RingHom.id Real)
    (finiteThroatGeneratorPatchSmoothEuclideanH1LinearMap
      period hPeriod analysis patch component)
    (llH1SmoothEmbedding period hPeriod
      (analysis.llH1Data period hPeriod)).toLinearMap

theorem finiteThroatGeneratorPatchEuclideanH1Localizer_agrees_on_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    finiteThroatGeneratorPatchEuclideanH1Localizer
        period hPeriod analysis patch component
        (llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) u) =
      finiteThroatGeneratorPatchSmoothEuclideanH1
        period hPeriod patch component u.toTest := by
  letI : IsBoundedSMul Real
      (FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch) :=
    @NormedSpace.toIsBoundedSMul
      Real (FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch)
      inferInstance inferInstance inferInstance
  unfold finiteThroatGeneratorPatchEuclideanH1Localizer
  apply LinearMap.extendOfNorm_eq
  · exact llH1SmoothEmbedding_denseRange period hPeriod
      (analysis.llH1Data period hPeriod)
  · obtain ⟨constant, hBound⟩ :=
      exists_finiteThroatGeneratorPatchSmoothEuclideanH1_bound
        period hPeriod analysis patch component
    refine ⟨constant, ?_⟩
    intro v
    change
      ‖finiteThroatGeneratorPatchSmoothEuclideanH1
          period hPeriod patch component v.toTest‖ ≤
        constant *
          ‖(v : LLH1Space period hPeriod
            (analysis.llH1Data period hPeriod))‖
    simpa only [UniformSpace.Completion.norm_coe] using hBound v

end
end P0EFTJanusProgramPT12LLCanonicalThroatSmoothRellichExtension4D
end JanusFormal

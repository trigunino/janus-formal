import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

/-!
# Reduced quotient of the full smooth LL core

Quotienting the full three-slot LL core by the auxiliary/measure directions
leaves exactly the reduced smooth LL field.  Its Friedrichs smooth-core map is
injective and dense in the canonical LL L² space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Full smooth LL directions with vanishing reduced field coordinate. -/
abbrev GlobalFullLLAuxMeasureSubmodule
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Submodule Real (GlobalFullLLSmooth period hPeriod analysis) :=
  LinearMap.ker
    (LinearMap.snd Real
      (GlobalLLAuxMeasureSmooth period hPeriod)
      (LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)))

theorem globalFullLLAuxMeasureSubmodule_eq_range_inl
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLAuxMeasureSubmodule period hPeriod analysis =
      LinearMap.range
        (LinearMap.inl Real
          (GlobalLLAuxMeasureSmooth period hPeriod)
          (LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod))) :=
  LinearMap.ker_snd Real
    (GlobalLLAuxMeasureSmooth period hPeriod)
    (LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod))

/-- The full smooth LL core modulo its auxiliary/measure directions. -/
abbrev GlobalFullLLReducedSmoothQuotient
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalFullLLSmooth period hPeriod analysis ⧸
    GlobalFullLLAuxMeasureSubmodule period hPeriod analysis

/-- The reduced quotient is exactly the smooth LL field coordinate. -/
def globalFullLLReducedSmoothQuotientEquiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLReducedSmoothQuotient period hPeriod analysis ≃ₗ[Real]
      LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod) :=
  (LinearMap.snd Real
      (GlobalLLAuxMeasureSmooth period hPeriod)
      (LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)))
    |>.quotKerEquivOfSurjective
      LinearMap.snd_surjective

@[simp]
theorem globalFullLLReducedSmoothQuotientEquiv_mk
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    globalFullLLReducedSmoothQuotientEquiv period hPeriod analysis
        (Submodule.Quotient.mk direction :
          GlobalFullLLReducedSmoothQuotient period hPeriod analysis) =
      direction.2 := by
  rfl

/-- The quotient core included into the canonical LL L² space. -/
def globalFullLLReducedSmoothQuotientToCanonicalLLL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLReducedSmoothQuotient period hPeriod analysis →ₗ[Real]
      CanonicalLLL2 period hPeriod analysis :=
  (llH1SmoothToFluxL2LinearMap period hPeriod
      (analysis.llH1Data period hPeriod)).comp
    (globalFullLLReducedSmoothQuotientEquiv
      period hPeriod analysis).toLinearMap

@[simp]
theorem globalFullLLReducedSmoothQuotientToCanonicalLLL2_mk
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    globalFullLLReducedSmoothQuotientToCanonicalLLL2
        period hPeriod analysis
          (Submodule.Quotient.mk direction :
            GlobalFullLLReducedSmoothQuotient period hPeriod analysis) =
      llH1SmoothToFluxL2 period hPeriod
        (analysis.llH1Data period hPeriod) direction.2 := by
  rfl

theorem globalFullLLReducedSmoothQuotientToCanonicalLLL2_eq_friedrichs_value
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLReducedSmoothQuotient
      period hPeriod analysis) :
    globalFullLLReducedSmoothQuotientToCanonicalLLL2
        period hPeriod analysis direction =
      ((canonicalLLFriedrichsSmoothDomainElement period hPeriod analysis
          (globalFullLLReducedSmoothQuotientEquiv
            period hPeriod analysis direction) :
            (canonicalLLFriedrichsJacobi
              period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis) := by
  rw [canonicalLLFriedrichsSmoothDomainElement_value]
  rfl

theorem globalFullLLReducedSmoothQuotientToCanonicalLLL2_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalFullLLReducedSmoothQuotientToCanonicalLLL2
        period hPeriod analysis) := by
  intro first second hEqual
  apply (globalFullLLReducedSmoothQuotientEquiv
    period hPeriod analysis).injective
  apply llH1SmoothEmbedding_injective period hPeriod
    (analysis.llH1Data period hPeriod)
  apply canonicalLLH1ToFluxL2_injective period hPeriod analysis
  rw [canonicalLLH1ToFluxL2_agrees_on_smooth,
    canonicalLLH1ToFluxL2_agrees_on_smooth]
  exact hEqual

theorem globalFullLLReducedSmoothQuotientToCanonicalLLL2_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange
      (globalFullLLReducedSmoothQuotientToCanonicalLLL2
        period hPeriod analysis) := by
  have hSmooth : DenseRange (fun direction =>
      llH1SmoothToFluxL2 period hPeriod
        (analysis.llH1Data period hPeriod) direction) := by
    have hComp : DenseRange (fun direction =>
        canonicalLLH1ToFluxL2 period hPeriod analysis
          (llH1SmoothEmbedding period hPeriod
            (analysis.llH1Data period hPeriod) direction)) :=
      (canonicalLLH1ToFluxL2_denseRange period hPeriod analysis).comp
        (llH1SmoothEmbedding_denseRange period hPeriod
          (analysis.llH1Data period hPeriod))
        (canonicalLLH1ToFluxL2 period hPeriod analysis).continuous
    simpa only [canonicalLLH1ToFluxL2_agrees_on_smooth] using hComp
  have hRange :
      Set.range
          (globalFullLLReducedSmoothQuotientToCanonicalLLL2
            period hPeriod analysis) =
        Set.range (fun direction =>
          llH1SmoothToFluxL2 period hPeriod
            (analysis.llH1Data period hPeriod) direction) := by
    ext value
    constructor
    · rintro ⟨quotientDirection, rfl⟩
      exact ⟨globalFullLLReducedSmoothQuotientEquiv
        period hPeriod analysis quotientDirection, rfl⟩
    · rintro ⟨direction, rfl⟩
      refine ⟨(globalFullLLReducedSmoothQuotientEquiv
        period hPeriod analysis).symm direction, ?_⟩
      simp [globalFullLLReducedSmoothQuotientToCanonicalLLL2]
      rfl
  rw [DenseRange, hRange]
  exact hSmooth

end
end P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D
end JanusFormal

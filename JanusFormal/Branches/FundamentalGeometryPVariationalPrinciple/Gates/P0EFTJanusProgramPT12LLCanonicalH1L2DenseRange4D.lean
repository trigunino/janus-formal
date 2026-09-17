import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

/-! The canonical LL energy completion has dense value image in throat L². -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Every smooth throat L² field is the value of a completed LL energy field. -/
theorem llSmoothToL2_range_subset_canonicalLLH1ToFluxL2_range
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Set.range (llSmoothToL2 period hPeriod) ⊆
      Set.range (canonicalLLH1ToFluxL2 period hPeriod analysis) := by
  rintro value ⟨direction, rfl⟩
  let u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod) :=
    ⟨direction⟩
  refine ⟨llH1SmoothEmbedding period hPeriod
    (analysis.llH1Data period hPeriod) u, ?_⟩
  rw [canonicalLLH1ToFluxL2_agrees_on_smooth]
  rfl

/-- The canonical LL H¹-to-L² value map has dense range. -/
theorem canonicalLLH1ToFluxL2_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange (canonicalLLH1ToFluxL2 period hPeriod analysis) := by
  intro value
  have hSmooth : value ∈ closure (Set.range (llSmoothToL2 period hPeriod)) :=
    llSmoothToL2_denseRange period hPeriod value
  apply (closure_minimal ?_ isClosed_closure) hSmooth
  exact (llSmoothToL2_range_subset_canonicalLLH1ToFluxL2_range
    period hPeriod analysis).trans subset_closure

/-- Exact closure of the canonical LL energy value image. -/
theorem canonicalLLH1ToFluxL2_closure_range_eq_univ
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    closure (Set.range (canonicalLLH1ToFluxL2 period hPeriod analysis)) =
      Set.univ :=
  (canonicalLLH1ToFluxL2_denseRange period hPeriod analysis).closure_range

end
end P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D
end JanusFormal

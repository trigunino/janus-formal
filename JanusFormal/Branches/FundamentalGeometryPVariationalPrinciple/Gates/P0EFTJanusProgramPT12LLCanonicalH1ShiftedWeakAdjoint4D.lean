import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D

/-!
# Adjoint realization of shifted weak LL solutions

Every shifted weak LL solution belongs to the adjoint domain of the existing
closed Jacobi operator. Its adjoint value is the expected shifted residual.
This does not identify the adjoint domain with the minimal closed domain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakAdjoint4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The weak equation and the closed-domain energy lift give the exact
adjoint pairing against every vector of the closed Jacobi domain. -/
theorem canonicalLLShiftedWeakL2Solution_closed_adjoint_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (f : CanonicalLLL2 period hPeriod analysis)
    (z : (canonicalLLClosedJacobi period hPeriod analysis).domain) :
    inner Real
        (f - shift •
          canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f)
        (z : CanonicalLLL2 period hPeriod analysis) =
      inner Real
        (canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f)
        (canonicalLLClosedJacobi period hPeriod analysis z) := by
  let I := canonicalLLH1ToFluxL2 period hPeriod analysis
  let u := canonicalLLShiftedWeakH1Solution period hPeriod analysis shift hShift f
  let x := canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f
  let C := canonicalLLClosedJacobi period hPeriod analysis
  obtain ⟨v, hv, hPair⟩ :=
    canonicalLLClosedJacobi_domain_has_energy_lift period hPeriod analysis z
  have hWeak := canonicalLLShiftedWeakH1Solution_pairing
    period hPeriod analysis shift hShift f v
  have hx : I u = x := rfl
  change inner Real u v + shift * inner Real x (I v) =
    inner Real f (I v) at hWeak
  have hRearranged :
      inner Real u v = inner Real f (I v) - shift * inner Real x (I v) := by
    linarith
  change inner Real (f - shift • x) (z : CanonicalLLL2 period hPeriod analysis) =
    inner Real x (C z)
  calc
    inner Real (f - shift • x) (z : CanonicalLLL2 period hPeriod analysis) =
        inner Real f (z : CanonicalLLL2 period hPeriod analysis) -
          shift * inner Real x (z : CanonicalLLL2 period hPeriod analysis) := by
            rw [inner_sub_left, real_inner_smul_left]
    _ = inner Real f (I v) - shift * inner Real x (I v) := by rw [hv]
    _ = inner Real u v := hRearranged.symm
    _ = inner Real v u := real_inner_comm _ _
    _ = inner Real (C z) (I u) := hPair u
    _ = inner Real (C z) x := by rw [hx]
    _ = inner Real x (C z) := real_inner_comm _ _

/-- Every shifted weak LL solution is in the maximal Hilbert-adjoint domain
of the same closed Jacobi operator. -/
theorem canonicalLLShiftedWeakL2Solution_mem_closed_adjoint_domain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (f : CanonicalLLL2 period hPeriod analysis) :
    canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f ∈
      (canonicalLLClosedJacobi period hPeriod analysis).adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨f - shift •
    canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f, ?_⟩
  exact canonicalLLShiftedWeakL2Solution_closed_adjoint_pairing
    period hPeriod analysis shift hShift f

/-- The adjoint sends the shifted weak solution to its unshifted residual. -/
theorem canonicalLLShiftedWeakL2Solution_closed_adjoint_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (f : CanonicalLLL2 period hPeriod analysis) :
    (canonicalLLClosedJacobi period hPeriod analysis).adjoint
        ⟨canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f,
          canonicalLLShiftedWeakL2Solution_mem_closed_adjoint_domain
            period hPeriod analysis shift hShift f⟩ =
      f - shift •
        canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f := by
  let data := analysis.llH1Data period hPeriod
  let C := canonicalLLClosedJacobi period hPeriod analysis
  have hDense : Dense (C.domain : Set (CanonicalLLL2 period hPeriod analysis)) :=
    (llJacobiSmoothPMap_denseDomain period hPeriod data.fields).mono
      (llJacobiSmoothPMap_le_closed period hPeriod data.fields).1
  apply LinearPMap.adjoint_apply_eq hDense
  exact canonicalLLShiftedWeakL2Solution_closed_adjoint_pairing
    period hPeriod analysis shift hShift f

end
end P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakAdjoint4D
end JanusFormal

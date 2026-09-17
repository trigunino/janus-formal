import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HilbertEnergyShift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosedShift4D

/-!
# Shifted weak LL solutions and the exact remaining domain obligation

On a positive LL background, every nonnegative shift has a bounded, unique
energy solution for every genuine L² source. Its L² value is a left inverse
on the existing reduced closed Jacobi domain.

The existing closed shift is surjective IF AND ONLY IF these explicit weak
solutions belong to that same domain. No equality between the minimal graph
closure and a weak/Friedrichs realization is postulated. Rellich compactness
is retained as an explicit premise in the compact-solution theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D
open P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D
open P0EFTJanusProgramPT12LLStrongJacobiClosedShift4D
open P0EFTJanusProgramPT12HilbertEnergyShift4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- An everywhere-defined solution in the positive canonical LL energy space. -/
def canonicalLLShiftedWeakH1Solution
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    CanonicalLLL2 period hPeriod analysis →L[Real]
      CanonicalLLEnergy period hPeriod analysis :=
  energyShiftSolution (canonicalLLH1ToFluxL2 period hPeriod analysis) shift hShift

/-- Its genuine throat L² value, not yet an inverse on the closed graph domain. -/
def canonicalLLShiftedWeakL2Solution
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    CanonicalLLL2 period hPeriod analysis →L[Real]
      CanonicalLLL2 period hPeriod analysis :=
  energyShiftL2Solution (canonicalLLH1ToFluxL2 period hPeriod analysis) shift hShift

/-- Exact weak equation for every source and every completed-energy test. -/
theorem canonicalLLShiftedWeakH1Solution_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (f : CanonicalLLL2 period hPeriod analysis)
    (v : CanonicalLLEnergy period hPeriod analysis) :
    inner Real (canonicalLLShiftedWeakH1Solution period hPeriod analysis shift hShift f) v +
        shift * inner Real
          (canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f)
          (canonicalLLH1ToFluxL2 period hPeriod analysis v) =
      inner Real f (canonicalLLH1ToFluxL2 period hPeriod analysis v) :=
  energyShiftSolution_pairing _ shift hShift f v

/-- Perform the shifted pairing calculation on a single Hilbert-space carrier,
without exposing any LL operator-domain or canonical-measure aliases to `rw`. -/
private theorem energyShiftL2Solution_eq_of_adjoint_value
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (I : V →L[Real] H) (shift : Real) (hShift : 0 ≤ shift)
    (x y : H) (hValue : I (I.adjoint y) = x) :
    energyShiftL2Solution I shift hShift (y + shift • x) = x := by
  have hSolution : I.adjoint y =
      energyShiftSolution I shift hShift (y + shift • x) := by
    apply energyShiftSolution_unique
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, hValue,
      inner_add_left, real_inner_smul_left]
  exact Eq.trans (congrArg I hSolution.symm) hValue

/-- The weak solution is a left inverse of the SAME closed reduced Jacobi shift. -/
theorem canonicalLLShiftedWeakL2Solution_closed_left_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (x : (canonicalLLClosedJacobi period hPeriod analysis).domain) :
    canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift
        (llJacobiShiftedPMap period hPeriod
          (analysis.llH1Data period hPeriod).fields shift x) =
      (x : CanonicalLLL2 period hPeriod analysis) := by
  let H : Type := CanonicalLLL2 period hPeriod analysis
  let I : CanonicalLLEnergy period hPeriod analysis →L[Real] H :=
    canonicalLLH1ToFluxL2 period hPeriod analysis
  let C : H →ₗ.[Real] H := canonicalLLClosedJacobi period hPeriod analysis
  have hValue : I (I.adjoint (C x)) = (x : H) :=
    canonicalLLWeakL2Inverse_closed_left_inverse period hPeriod analysis x
  -- The shifted source is definitionally C x + shift • x. Use ordinary term
  -- elaboration here, not a rewrite across its two dependent domain aliases.
  exact energyShiftL2Solution_eq_of_adjoint_value I shift hShift
    (x : H) (C x) hValue

theorem canonicalLLShiftedWeakL2Solution_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    Function.Injective
      (canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift) :=
  energyShiftL2Solution_injective _
    (canonicalLLH1ToFluxL2_injective period hPeriod analysis)
    (canonicalLLH1ToFluxL2_denseRange period hPeriod analysis) shift hShift

/-- Actual strong solvability follows once the explicit weak solution belongs
to the original closed domain; no new operator realization is substituted. -/
theorem canonicalLLShiftedWeakL2Solution_right_inverse_of_mem_domain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (f : CanonicalLLL2 period hPeriod analysis)
    (hDomain : canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f ∈
      (canonicalLLClosedJacobi period hPeriod analysis).domain) :
    llJacobiShiftedPMap period hPeriod
        (analysis.llH1Data period hPeriod).fields shift
        ⟨canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f, hDomain⟩ =
      f := by
  apply canonicalLLShiftedWeakL2Solution_injective period hPeriod analysis shift hShift
  exact canonicalLLShiftedWeakL2Solution_closed_left_inverse period hPeriod analysis
    shift hShift ⟨_, hDomain⟩

/-- Exact remaining surjectivity obligation: membership in the existing graph
closure for ALL weak L² solutions. This equivalence does not discharge it. -/
theorem canonicalLLJacobiShifted_surjective_iff_weak_domain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    Function.Surjective (llJacobiShiftedPMap period hPeriod
        (analysis.llH1Data period hPeriod).fields shift).toFun ↔
      ∀ f : CanonicalLLL2 period hPeriod analysis,
        canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift f ∈
          (canonicalLLClosedJacobi period hPeriod analysis).domain := by
  constructor
  · intro hSurjective f
    obtain ⟨x, hx⟩ := hSurjective f
    have hLeft := canonicalLLShiftedWeakL2Solution_closed_left_inverse
      period hPeriod analysis shift hShift x
    change canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift
      ((llJacobiShiftedPMap period hPeriod
        (analysis.llH1Data period hPeriod).fields shift).toFun x) = _ at hLeft
    rw [hx] at hLeft
    rw [hLeft]
    exact x.property
  · intro hDomain f
    refine ⟨⟨_, hDomain f⟩, ?_⟩
    exact canonicalLLShiftedWeakL2Solution_right_inverse_of_mem_domain
      period hPeriod analysis shift hShift f (hDomain f)

/-- Compactness of weak shifted solutions is a CONSEQUENCE of actual Rellich
compactness, not a proof of the missing throat Rellich theorem. -/
theorem canonicalLLShiftedWeakL2Solution_compact_of_rellich
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hRellich : IsCompactOperator (canonicalLLH1ToFluxL2 period hPeriod analysis))
    (shift : Real) (hShift : 0 ≤ shift) :
    IsCompactOperator
      (canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift) :=
  energyShiftL2Solution_compact _ hRellich shift hShift

end
end P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D
end JanusFormal

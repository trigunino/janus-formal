import Mathlib.Analysis.Normed.Module.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramBasis4D

/-!
# Positive lower bounds for injective finite synthesis

For a finite family in a real normed space, coefficient synthesis is injective
exactly when the family is linearly independent.  Since the coefficient space
is finite-dimensional, every injective synthesis map is anti-Lipschitz and
therefore admits a positive norm lower bound

`m * ‖c‖ ≤ ‖S(c)‖`.

The existence theorem and its canonical choice below are used for the original
named Candidate-A kernel subfamilies.  Thus their pointwise lower bound is not a
new mathematical premise; only uniform control of that bound along the family
can remain analytic input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteFamilySynthesisLowerBound4D

set_option autoImplicit false
noncomputable section

open Function
open scoped BigOperators
open P0EFTJanusProgramPFiniteFamilyGramBasis4D

variable {Index E : Type*}
  [Fintype Index] [DecidableEq Index]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Injectivity of finite coefficient synthesis is equivalent to linear
independence of the vector family. -/
theorem finiteFamilySynthesis_injective_iff_linearIndependent
    (vectors : Index → E) :
    Function.Injective (finiteFamilySynthesis vectors) ↔
      LinearIndependent Real vectors := by
  constructor
  · intro hInjective
    rw [Fintype.linearIndependent_iff]
    intro coefficient hZero index
    have hEqual :
        finiteFamilySynthesis vectors coefficient =
          finiteFamilySynthesis vectors 0 := by
      simpa [finiteFamilySynthesis] using hZero
    have hCoefficient := hInjective hEqual
    simpa using congrFun hCoefficient index
  · intro hIndependent first second hEqual
    rw [Fintype.linearIndependent_iff] at hIndependent
    have hDifference :
        finiteFamilySynthesis vectors (first - second) = 0 := by
      rw [map_sub, hEqual, sub_self]
    have hCoefficientZero : ∀ index, (first - second) index = 0 :=
      hIndependent (first - second) (by
        simpa [finiteFamilySynthesis] using hDifference)
    ext index
    exact sub_eq_zero.mp (hCoefficientZero index)

/-- Every injective finite synthesis map has a positive coefficient lower
bound. -/
theorem exists_finiteFamilySynthesis_lower_bound_of_injective
    (vectors : Index → E)
    (hInjective : Function.Injective (finiteFamilySynthesis vectors)) :
    ∃ lowerConstant : Real, 0 < lowerConstant ∧
      ∀ coefficient,
        lowerConstant * ‖coefficient‖ ≤
          ‖finiteFamilySynthesis vectors coefficient‖ := by
  have hAntilipschitz :
      ∃ K, AntilipschitzWith K (finiteFamilySynthesis vectors) := by
    obtain ⟨K, _hKPos, hK⟩ :=
      (finiteFamilySynthesis vectors).injective_iff_antilipschitz.mp hInjective
    exact ⟨K, hK⟩
  exact antilipschitzWith_iff_exists_mul_le_norm.mp hAntilipschitz

/-- A noncomputably selected positive lower-bound constant for one injective
finite synthesis map. -/
def finiteFamilySynthesisLowerConstant
    (vectors : Index → E)
    (hInjective : Function.Injective (finiteFamilySynthesis vectors)) : Real :=
  Classical.choose
    (exists_finiteFamilySynthesis_lower_bound_of_injective vectors hInjective)

/-- Positivity of the selected synthesis lower-bound constant. -/
theorem finiteFamilySynthesisLowerConstant_pos
    (vectors : Index → E)
    (hInjective : Function.Injective (finiteFamilySynthesis vectors)) :
    0 < finiteFamilySynthesisLowerConstant vectors hInjective :=
  (Classical.choose_spec
    (exists_finiteFamilySynthesis_lower_bound_of_injective vectors hInjective)).1

/-- Lower estimate supplied by the selected constant. -/
theorem finiteFamilySynthesisLowerConstant_mul_norm_le
    (vectors : Index → E)
    (hInjective : Function.Injective (finiteFamilySynthesis vectors))
    (coefficient : Index → Real) :
    finiteFamilySynthesisLowerConstant vectors hInjective * ‖coefficient‖ ≤
      ‖finiteFamilySynthesis vectors coefficient‖ :=
  (Classical.choose_spec
    (exists_finiteFamilySynthesis_lower_bound_of_injective vectors hInjective)).2
      coefficient

/-- Public finite synthesis lower-bound checkpoint. -/
theorem finite_family_synthesis_lower_bound_gate
    (vectors : Index → E)
    (hIndependent : LinearIndependent Real vectors) :
    ∃ lowerConstant : Real, 0 < lowerConstant ∧
      (∀ coefficient,
        lowerConstant * ‖coefficient‖ ≤
          ‖finiteFamilySynthesis vectors coefficient‖) ∧
      Function.Injective (finiteFamilySynthesis vectors) := by
  have hInjective :=
    (finiteFamilySynthesis_injective_iff_linearIndependent vectors).mpr
      hIndependent
  exact
    ⟨finiteFamilySynthesisLowerConstant vectors hInjective,
      finiteFamilySynthesisLowerConstant_pos vectors hInjective,
      finiteFamilySynthesisLowerConstant_mul_norm_le vectors hInjective,
      hInjective⟩

end
end P0EFTJanusProgramPFiniteFamilySynthesisLowerBound4D
end JanusFormal
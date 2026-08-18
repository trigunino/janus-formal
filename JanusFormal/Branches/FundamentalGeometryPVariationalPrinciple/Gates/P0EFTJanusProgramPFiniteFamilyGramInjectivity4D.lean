import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramBasis4D

/-!
# Gram injectivity from linear independence

For a finite family in a real inner-product space, injectivity of coefficient
synthesis implies injectivity of the Gram endomorphism.  Combined with the
preceding converse, Gram nondegeneracy is exactly the finite coefficient
criterion for linear independence.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteFamilyGramInjectivity4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteFamilyGramBasis4D

variable {Index E : Type*}
  [Fintype Index] [DecidableEq Index]
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- If coefficient synthesis is injective, then the Gram endomorphism is
injective. -/
theorem finiteFamilyGramMap_injective_of_synthesis_injective
    (vectors : Index → E)
    (hSynthesis : Function.Injective (finiteFamilySynthesis vectors)) :
    Function.Injective (finiteFamilyGramMap vectors) := by
  intro first second hGram
  apply hSynthesis
  let firstVector := finiteFamilySynthesis vectors first
  let secondVector := finiteFamilySynthesis vectors second
  let difference := firstVector - secondVector
  have hOrthogonal : ∀ index,
      inner Real difference (vectors index) = 0 := by
    intro index
    have hCoordinate := congrFun hGram index
    change inner Real firstVector (vectors index) =
      inner Real secondVector (vectors index) at hCoordinate
    simpa [difference, inner_sub_left] using sub_eq_zero.mpr hCoordinate
  have hDifferenceExpansion :
      difference = finiteFamilySynthesis vectors (first - second) := by
    simp [difference, firstVector, secondVector]
  have hSelf : inner Real difference difference = 0 := by
    calc
      inner Real difference difference =
          inner Real difference
            (finiteFamilySynthesis vectors (first - second)) :=
        congrArg (fun vector => inner Real difference vector)
          hDifferenceExpansion
      _ = 0 := by
        change inner Real difference
          (∑ index, (first - second) index • vectors index) = 0
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro index _
        rw [inner_smul_right, hOrthogonal index]
        simp
  have hDifferenceZero : difference = 0 := by
    exact inner_self_eq_zero.mp hSelf
  exact sub_eq_zero.mp hDifferenceZero

/-- For a finite family, Gram injectivity and synthesis injectivity are
equivalent. -/
theorem finiteFamilyGramMap_injective_iff_synthesis_injective
    (vectors : Index → E) :
    Function.Injective (finiteFamilyGramMap vectors) ↔
      Function.Injective (finiteFamilySynthesis vectors) := by
  constructor
  · exact finiteFamilySynthesis_injective_of_gram_injective vectors
  · exact finiteFamilyGramMap_injective_of_synthesis_injective vectors

/-- Public Gram/linear-independence coefficient checkpoint. -/
theorem finite_family_gram_injectivity_gate
    (vectors : Index → E) :
    Function.Injective (finiteFamilyGramMap vectors) ↔
      Function.Injective (finiteFamilySynthesis vectors) :=
  finiteFamilyGramMap_injective_iff_synthesis_injective vectors

end
end P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
end JanusFormal

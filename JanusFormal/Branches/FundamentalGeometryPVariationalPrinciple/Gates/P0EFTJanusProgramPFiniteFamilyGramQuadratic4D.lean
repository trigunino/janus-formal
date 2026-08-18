import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramInjectivity4D

/-!
# Quadratic form of a finite Gram family

For a finite family `v_i` in a real inner-product space, coefficient synthesis
and the coefficient Gram endomorphism satisfy

`c dot G(c) = <S(c), S(c)> = ‖S(c)‖^2`.

Thus a positive quadratic lower estimate for the Gram form forces coefficient
synthesis to be injective.  This is the finite analytic criterion used to turn
sectorwise Candidate-A coercivity estimates into genuine noncrossing of the
physical zero-mode Gram blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteFamilyGramQuadratic4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPFiniteFamilyGramInjectivity4D

variable {Index E : Type*}
  [Fintype Index] [DecidableEq Index]
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- The coefficient Gram quadratic form is the inner square of coefficient
synthesis. -/
theorem finiteFamilyGramQuadratic_eq_inner_synthesis
    (vectors : Index → E) (coefficient : Index → Real) :
    dotProduct coefficient (finiteFamilyGramMap vectors coefficient) =
      inner Real
        (finiteFamilySynthesis vectors coefficient)
        (finiteFamilySynthesis vectors coefficient) := by
  unfold dotProduct
  simp only [finiteFamilyGramMap_apply]
  rw [show finiteFamilySynthesis vectors coefficient =
    ∑ index, coefficient index • vectors index from rfl]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [inner_smul_right]

/-- Norm-square form of the finite Gram quadratic identity. -/
theorem finiteFamilyGramQuadratic_eq_norm_sq
    (vectors : Index → E) (coefficient : Index → Real) :
    dotProduct coefficient (finiteFamilyGramMap vectors coefficient) =
      ‖finiteFamilySynthesis vectors coefficient‖ ^ 2 := by
  rw [finiteFamilyGramQuadratic_eq_inner_synthesis]
  exact inner_self_eq_norm_sq_to_K _

/-- A positive lower quadratic estimate for the coefficient Gram form forces
coefficient synthesis to be injective. -/
theorem finiteFamilySynthesis_injective_of_gramQuadratic_lower_bound
    (vectors : Index → E)
    (lowerConstant : Real) (hLowerConstant : 0 < lowerConstant)
    (hLower : ∀ coefficient,
      lowerConstant * ‖coefficient‖ ^ 2 ≤
        dotProduct coefficient (finiteFamilyGramMap vectors coefficient)) :
    Function.Injective (finiteFamilySynthesis vectors) := by
  intro first second hEqual
  have hDifference :
      finiteFamilySynthesis vectors (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hQuadratic := hLower (first - second)
  rw [finiteFamilyGramQuadratic_eq_norm_sq, hDifference, norm_zero] at hQuadratic
  have hSquareNonpos : ‖first - second‖ ^ 2 ≤ 0 := by
    exact nonpos_of_mul_nonpos_right (by simpa using hQuadratic) hLowerConstant
  have hNormZero : ‖first - second‖ = 0 :=
    (sq_nonpos_iff ‖first - second‖).mp hSquareNonpos
  exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)

/-- The same quadratic estimate forces injectivity of the Gram endomorphism. -/
theorem finiteFamilyGramMap_injective_of_gramQuadratic_lower_bound
    (vectors : Index → E)
    (lowerConstant : Real) (hLowerConstant : 0 < lowerConstant)
    (hLower : ∀ coefficient,
      lowerConstant * ‖coefficient‖ ^ 2 ≤
        dotProduct coefficient (finiteFamilyGramMap vectors coefficient)) :
    Function.Injective (finiteFamilyGramMap vectors) :=
  finiteFamilyGramMap_injective_of_synthesis_injective vectors
    (finiteFamilySynthesis_injective_of_gramQuadratic_lower_bound vectors
      lowerConstant hLowerConstant hLower)

/-- Public finite Gram-quadratic checkpoint. -/
theorem finite_family_gram_quadratic_gate
    (vectors : Index → E)
    (lowerConstant : Real) (hLowerConstant : 0 < lowerConstant)
    (hLower : ∀ coefficient,
      lowerConstant * ‖coefficient‖ ^ 2 ≤
        dotProduct coefficient (finiteFamilyGramMap vectors coefficient)) :
    (∀ coefficient,
      dotProduct coefficient (finiteFamilyGramMap vectors coefficient) =
        ‖finiteFamilySynthesis vectors coefficient‖ ^ 2) ∧
    Function.Injective (finiteFamilySynthesis vectors) ∧
    Function.Injective (finiteFamilyGramMap vectors) :=
  ⟨finiteFamilyGramQuadratic_eq_norm_sq vectors,
    finiteFamilySynthesis_injective_of_gramQuadratic_lower_bound vectors
      lowerConstant hLowerConstant hLower,
    finiteFamilyGramMap_injective_of_gramQuadratic_lower_bound vectors
      lowerConstant hLowerConstant hLower⟩

end
end P0EFTJanusProgramPFiniteFamilyGramQuadratic4D
end JanusFormal

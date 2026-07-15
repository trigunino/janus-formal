import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusPTFlatBimetricVariationalBridge

set_option autoImplicit false

open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Actual derivative of the positive shape polynomial. -/
def relativeShapeDerivative (beta1 beta2 c : ℝ) : ℝ :=
  4 * beta1 * (2 * c + 1) + 6 * beta2 * (c + 1)

theorem relativeShape_hasDerivAt
    (beta1 beta2 c : ℝ) :
    HasDerivAt (relativeShape beta1 beta2)
      (relativeShapeDerivative beta1 beta2 c) c := by
  have hFirst :
      HasDerivAt (fun x : ℝ => x ^ 2 + x + 1) (2 * c + 1) c := by
    simpa [id] using
      (((hasDerivAt_id c).pow 2).add (hasDerivAt_id c)).add_const 1
  have hSecond :
      HasDerivAt ((fun x : ℝ => x + 1) ^ 2) (2 * (c + 1)) c := by
    simpa [id] using ((hasDerivAt_id c).add_const 1).pow 2
  unfold relativeShape relativeShapeDerivative
  convert (hFirst.const_mul (4 * beta1)).add
    (hSecond.const_mul (3 * beta2)) using 1
  all_goals
    first
    | rfl
    | ring

/-- Actual force along the PT-flat proportional bimetric branch. -/
def proportionalInteractionForce (beta1 beta2 c : ℝ) : ℝ :=
  2 * (c - 1) * relativeShape beta1 beta2 c +
    (c - 1) ^ 2 * relativeShapeDerivative beta1 beta2 c

/-- The reduced PT-flat interaction energy has its displayed force as its
genuine derivative, rather than only as a formal polynomial expression. -/
theorem proportionalInteractionEnergy_hasDerivAt
    (beta1 beta2 c : ℝ) :
    HasDerivAt (proportionalInteractionEnergy beta1 beta2)
      (proportionalInteractionForce beta1 beta2 c) c := by
  have hSquare :
      HasDerivAt ((fun x : ℝ => x - 1) ^ 2) (2 * (c - 1)) c := by
    simpa [id] using ((hasDerivAt_id c).sub_const 1).pow 2
  have hProduct := hSquare.mul (relativeShape_hasDerivAt beta1 beta2 c)
  rw [show proportionalInteractionEnergy beta1 beta2 =
      fun x => (x - 1) ^ 2 * relativeShape beta1 beta2 x from
    funext (interaction_energy_factorization beta1 beta2)]
  unfold proportionalInteractionForce
  exact hProduct

/-- The exchange-symmetric proportional point is genuinely stationary. -/
theorem proportionalInteractionEnergy_hasDerivAt_symmetric_point
    (beta1 beta2 : ℝ) :
    HasDerivAt (proportionalInteractionEnergy beta1 beta2) 0 1 := by
  simpa [proportionalInteractionForce] using
    proportionalInteractionEnergy_hasDerivAt beta1 beta2 1

theorem relativeShapeDerivative_hasDerivAt
    (beta1 beta2 c : ℝ) :
    HasDerivAt (relativeShapeDerivative beta1 beta2)
      (8 * beta1 + 6 * beta2) c := by
  unfold relativeShapeDerivative
  convert
    (((hasDerivAt_id c).const_mul 2).add_const 1).const_mul (4 * beta1) |>.add
      (((hasDerivAt_id c).add_const 1).const_mul (6 * beta2)) using 1
  all_goals
    first
    | rfl
    | ring

/-- The actual derivative of the force at the symmetric point is twice the
positive shape there. -/
theorem proportionalInteractionForce_hasDerivAt_symmetric_point
    (beta1 beta2 : ℝ) :
    HasDerivAt (proportionalInteractionForce beta1 beta2)
      (2 * relativeShape beta1 beta2 1) 1 := by
  have hDisplacement : HasDerivAt (fun c : ℝ => c - 1) 1 1 :=
    (hasDerivAt_id 1).sub_const 1
  have hFirst := (hDisplacement.const_mul 2).mul
    (relativeShape_hasDerivAt beta1 beta2 1)
  have hSecond := hDisplacement.pow 2 |>.mul
    (relativeShapeDerivative_hasDerivAt beta1 beta2 1)
  unfold proportionalInteractionForce
  convert hFirst.add hSecond using 1
  all_goals
    first
    | rfl
    | norm_num

/-- The reduced Hessian is exactly twelve times the Fierz--Pauli mass
combination of the PT-flat coefficient family. -/
theorem symmetric_hessian_eq_twelve_fp_mass
    (beta1 beta2 : ℝ) :
    2 * relativeShape beta1 beta2 1 =
      12 * fpMassCombination (ptFlatCoefficients beta1 beta2) := by
  rw [pt_flat_fp_mass_combination]
  simp [relativeShape]
  ring

/-- The genuine second derivative of the reduced interaction energy at the
symmetric point is twelve times the Fierz--Pauli mass combination. -/
theorem proportionalInteractionEnergy_second_hasDerivAt_symmetric_point
    (beta1 beta2 : ℝ) :
    HasDerivAt
      (fun c => deriv (proportionalInteractionEnergy beta1 beta2) c)
      (12 * fpMassCombination (ptFlatCoefficients beta1 beta2)) 1 := by
  have hDeriv :
      (fun c => deriv (proportionalInteractionEnergy beta1 beta2) c) =
        proportionalInteractionForce beta1 beta2 := by
    funext c
    exact (proportionalInteractionEnergy_hasDerivAt beta1 beta2 c).deriv
  rw [hDeriv, ← symmetric_hessian_eq_twelve_fp_mass]
  exact proportionalInteractionForce_hasDerivAt_symmetric_point beta1 beta2

theorem proportionalInteractionEnergy_second_deriv_symmetric_point
    (beta1 beta2 : ℝ) :
    deriv (fun c => deriv (proportionalInteractionEnergy beta1 beta2) c) 1 =
      12 * fpMassCombination (ptFlatCoefficients beta1 beta2) :=
  (proportionalInteractionEnergy_second_hasDerivAt_symmetric_point
    beta1 beta2).deriv

/-- The symmetric proportional point has positive actual Hessian throughout
the selected positive coefficient cone. -/
theorem symmetric_hessian_positive
    (beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2) :
    0 < 2 * relativeShape beta1 beta2 1 := by
  exact mul_pos (by norm_num)
    (relative_shape_positive beta1 beta2 1 hBeta1 hBeta2 (by norm_num))

/-- On the positive proportional branch, `c = 1` is the unique global
minimizer of the actual reduced interaction energy.  This is a concrete
one-dimensional bimetric sector, not the full Janus metric field space. -/
theorem symmetric_point_unique_positive_global_minimizer
    (beta1 beta2 c : ℝ)
    (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2) (hC : 0 < c) :
    proportionalInteractionEnergy beta1 beta2 1 ≤
        proportionalInteractionEnergy beta1 beta2 c ∧
      (proportionalInteractionEnergy beta1 beta2 c =
          proportionalInteractionEnergy beta1 beta2 1 ↔ c = 1) := by
  have hAtOne := interaction_energy_at_symmetric_point beta1 beta2
  constructor
  · rw [hAtOne]
    by_cases hOne : c = 1
    · subst c
      rw [hAtOne]
    · exact le_of_lt
        (interaction_energy_positive_away_from_symmetric_point
          beta1 beta2 c hBeta1 hBeta2 hC hOne)
  · constructor
    · intro hEqual
      by_contra hOne
      have hPositive := interaction_energy_positive_away_from_symmetric_point
        beta1 beta2 c hBeta1 hBeta2 hC hOne
      rw [hAtOne] at hEqual
      linarith
    · intro hOne
      subst c
      rfl

end P0EFTJanusPTFlatBimetricVariationalBridge
end JanusFormal

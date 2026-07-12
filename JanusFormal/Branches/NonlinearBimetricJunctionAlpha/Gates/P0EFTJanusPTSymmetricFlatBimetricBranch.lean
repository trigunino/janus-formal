import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusReciprocalBimetricPotential

namespace JanusFormal
namespace P0EFTJanusPTSymmetricFlatBimetricBranch

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential

/--
A two-parameter PT-symmetric coefficient family with a flat proportional branch
at `c = 1`.
-/
def ptFlatCoefficients (beta1 beta2 : ℝ) : PotentialCoefficients :=
  { beta0 := -4 * beta1 - 3 * beta2
    beta1 := beta1
    beta2 := beta2
    beta3 := beta1
    beta4 := -4 * beta1 - 3 * beta2 }

/-- The family is fixed by metric exchange. -/
theorem pt_flat_coefficients_are_symmetric
    (beta1 beta2 : ℝ) :
    PTSymmetric (ptFlatCoefficients beta1 beta2) := by
  constructor <;> rfl

/-- Positive interaction energy is the negative of the potential convention. -/
def proportionalInteractionEnergy
    (beta1 beta2 c : ℝ) : ℝ :=
  -proportionalPotential (ptFlatCoefficients beta1 beta2) c

/-- Positive shape polynomial controlling the relative proportional mode. -/
def relativeShape (beta1 beta2 c : ℝ) : ℝ :=
  4 * beta1 * (c ^ 2 + c + 1) +
    3 * beta2 * (c + 1) ^ 2

/-- Exact factorization around the PT-symmetric proportional point. -/
theorem interaction_energy_factorization
    (beta1 beta2 c : ℝ) :
    proportionalInteractionEnergy beta1 beta2 c =
      (c - 1) ^ 2 * relativeShape beta1 beta2 c := by
  unfold proportionalInteractionEnergy proportionalPotential
    ptFlatCoefficients relativeShape
  ring

/-- The proportional interaction energy vanishes at `c = 1`. -/
theorem interaction_energy_at_symmetric_point
    (beta1 beta2 : ℝ) :
    proportionalInteractionEnergy beta1 beta2 1 = 0 := by
  rw [interaction_energy_factorization]
  norm_num

/-- Positive `beta1` and nonnegative `beta2` make the shape positive for `c > 0`. -/
theorem relative_shape_positive
    (beta1 beta2 c : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (hC : 0 < c) :
    0 < relativeShape beta1 beta2 c := by
  have hFirstPolynomial : 0 < c ^ 2 + c + 1 := by
    nlinarith [sq_nonneg c]
  have hSecondPolynomial : 0 ≤ (c + 1) ^ 2 :=
    sq_nonneg (c + 1)
  have hFirstTerm :
      0 < 4 * beta1 * (c ^ 2 + c + 1) :=
    mul_pos (mul_pos (by norm_num) hBeta1) hFirstPolynomial
  have hSecondTerm :
      0 ≤ 3 * beta2 * (c + 1) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by norm_num) hBeta2)
      hSecondPolynomial
  unfold relativeShape
  exact add_pos_of_pos_of_nonneg hFirstTerm hSecondTerm

/-- `c = 1` is the unique positive zero and strict positive minimum of the energy. -/
theorem interaction_energy_positive_away_from_symmetric_point
    (beta1 beta2 c : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (hC : 0 < c)
    (hNotOne : c ≠ 1) :
    0 < proportionalInteractionEnergy beta1 beta2 c := by
  rw [interaction_energy_factorization]
  have hSquare : 0 < (c - 1) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hNotOne)
  exact mul_pos hSquare (relative_shape_positive beta1 beta2 c hBeta1 hBeta2 hC)

/-- Fierz--Pauli coefficient on the symmetric proportional branch. -/
def fpMassCombination (b : PotentialCoefficients) : ℝ :=
  b.beta1 + 2 * b.beta2 + b.beta3

/-- The PT-flat family has mass combination `2*(beta1+beta2)`. -/
theorem pt_flat_fp_mass_combination
    (beta1 beta2 : ℝ) :
    fpMassCombination (ptFlatCoefficients beta1 beta2) =
      2 * (beta1 + beta2) := by
  unfold fpMassCombination ptFlatCoefficients
  ring

/-- The massive relative mode has positive mass coefficient in the selected cone. -/
theorem pt_flat_fp_mass_positive
    (beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2) :
    0 < fpMassCombination (ptFlatCoefficients beta1 beta2) := by
  rw [pt_flat_fp_mass_combination]
  nlinarith

/-- Two positive Einstein--Hilbert kinetic coefficients. -/
def positiveSpinTwoKinetic
    (planckPlusSquared planckMinusSquared hPlus hMinus : ℝ) : ℝ :=
  planckPlusSquared * hPlus ^ 2 +
    planckMinusSquared * hMinus ^ 2

/-- Positive kinetic coefficients give a positive quadratic form off the origin. -/
theorem positive_spin_two_kinetic_is_definite
    (planckPlusSquared planckMinusSquared hPlus hMinus : ℝ)
    (hPlanckPlus : 0 < planckPlusSquared)
    (hPlanckMinus : 0 < planckMinusSquared)
    (hMode : hPlus ≠ 0 ∨ hMinus ≠ 0) :
    0 < positiveSpinTwoKinetic
      planckPlusSquared planckMinusSquared hPlus hMinus := by
  unfold positiveSpinTwoKinetic
  rcases hMode with hPlusNonzero | hMinusNonzero
  · have hPositivePlus :
        0 < planckPlusSquared * hPlus ^ 2 :=
      mul_pos hPlanckPlus (sq_pos_of_ne_zero hPlusNonzero)
    have hNonnegativeMinus :
        0 ≤ planckMinusSquared * hMinus ^ 2 :=
      mul_nonneg (le_of_lt hPlanckMinus) (sq_nonneg hMinus)
    exact add_pos_of_pos_of_nonneg hPositivePlus hNonnegativeMinus
  · have hNonnegativePlus :
        0 ≤ planckPlusSquared * hPlus ^ 2 :=
      mul_nonneg (le_of_lt hPlanckPlus) (sq_nonneg hPlus)
    have hPositiveMinus :
        0 < planckMinusSquared * hMinus ^ 2 :=
      mul_pos hPlanckMinus (sq_pos_of_ne_zero hMinusNonzero)
    exact add_pos_of_nonneg_of_pos hNonnegativePlus hPositiveMinus

/--
A linearly safe candidate branch: both spin-2 kinetic terms are positive, while
PT/negative-mass information must reside in matter and boundary charges rather
than in a negative-energy graviton.
-/
structure SafePTFlatBranch where
  beta1 : ℝ
  beta2 : ℝ
  planckPlusSquared : ℝ
  planckMinusSquared : ℝ
  beta1Positive : 0 < beta1
  beta2Nonnegative : 0 ≤ beta2
  planckPlusPositive : 0 < planckPlusSquared
  planckMinusPositive : 0 < planckMinusSquared
  ptOddMatterChargeDerived : Prop
  janusNewtonianLimitDerived : Prop
  nonlinearConstraintProofImported : Prop
  nullJunctionDerived : Prop

end P0EFTJanusPTSymmetricFlatBimetricBranch
end JanusFormal

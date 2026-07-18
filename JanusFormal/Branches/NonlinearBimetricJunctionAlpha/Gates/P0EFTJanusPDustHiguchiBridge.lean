import Mathlib

namespace JanusFormal
namespace P0EFTJanusPDustHiguchiBridge

set_option autoImplicit false

noncomputable section

def witnessHubble : ℝ := -(1 / 6)

def symmetricWitnessGap (massSquared : ℝ) : ℝ :=
  2 * (1 / 6 : ℝ) ^ 4 * (massSquared - (1 / 6 : ℝ) ^ 2)

theorem witnessHubble_abs : |witnessHubble| = 1 / 6 := by
  norm_num [witnessHubble]

theorem symmetricWitnessGap_positive_iff (massSquared : ℝ) :
    0 < symmetricWitnessGap massSquared ↔ 1 / 36 < massSquared := by
  unfold symmetricWitnessGap
  norm_num

theorem unit_mass_gap_exact :
    symmetricWitnessGap 1 = 35 / 23328 := by
  norm_num [symmetricWitnessGap]

def twoHubbleGap (hPlus hMinus massSquared : ℝ) : ℝ :=
  massSquared / 2 * (hPlus ^ 2 + hMinus ^ 2) ^ 2 -
    2 * hPlus ^ 3 * hMinus ^ 3

theorem twoHubbleGap_positive_of_product_lt_mass
    (hPlus hMinus massSquared : ℝ)
    (hPlusPos : 0 < hPlus) (hMinusPos : 0 < hMinus)
    (hProduct : hPlus * hMinus < massSquared) :
    0 < twoHubbleGap hPlus hMinus massSquared := by
  have hSquares : 4 * hPlus ^ 2 * hMinus ^ 2 ≤
      (hPlus ^ 2 + hMinus ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (hPlus ^ 2 - hMinus ^ 2)]
  have hProductPos : 0 < hPlus ^ 2 * hMinus ^ 2 := by positivity
  have hMassPos : 0 < massSquared :=
    lt_trans (mul_pos hPlusPos hMinusPos) hProduct
  have hBase : 0 <
      2 * hPlus ^ 2 * hMinus ^ 2 *
        (massSquared - hPlus * hMinus) := by positivity
  have hRemainder : 0 ≤ massSquared / 2 *
      ((hPlus ^ 2 + hMinus ^ 2) ^ 2 -
        4 * hPlus ^ 2 * hMinus ^ 2) := by positivity
  rw [show twoHubbleGap hPlus hMinus massSquared =
      2 * hPlus ^ 2 * hMinus ^ 2 *
          (massSquared - hPlus * hMinus) +
        massSquared / 2 * ((hPlus ^ 2 + hMinus ^ 2) ^ 2 -
          4 * hPlus ^ 2 * hMinus ^ 2) by
    unfold twoHubbleGap
    ring]
  positivity

theorem unit_mass_witness_box
    (hPlus hMinus epsilon : ℝ)
    (epsilonSmall : epsilon < 1 / 6)
    (hPlusBox : |hPlus - 1 / 6| ≤ epsilon)
    (hMinusBox : |hMinus - 1 / 6| ≤ epsilon) :
    0 < twoHubbleGap hPlus hMinus 1 := by
  have hPlusLower : 0 < hPlus := by
    rw [abs_le] at hPlusBox
    linarith
  have hMinusLower : 0 < hMinus := by
    rw [abs_le] at hMinusBox
    linarith
  have hPlusUpper : hPlus < 1 / 3 := by
    rw [abs_le] at hPlusBox
    linarith
  have hMinusUpper : hMinus < 1 / 3 := by
    rw [abs_le] at hMinusBox
    linarith
  apply twoHubbleGap_positive_of_product_lt_mass hPlus hMinus 1
    hPlusLower hMinusLower
  nlinarith

end
end P0EFTJanusPDustHiguchiBridge
end JanusFormal

import Mathlib

namespace JanusFormal
namespace P0EFTJanusLambda3BetaCombination

set_option autoImplicit false

def linearMixing (beta1 beta2 beta3 : ℝ) : ℝ :=
  beta1 + 2 * beta2 + beta3

def quadraticMixing (beta2 beta3 : ℝ) : ℝ :=
  beta2 + beta3

theorem pt_mixing_ratio
    (beta1 beta2 : ℝ) (hSum : beta1 + beta2 ≠ 0) :
    quadraticMixing beta2 beta1 / linearMixing beta1 beta2 beta1 = 1 / 2 := by
  rw [show quadraticMixing beta2 beta1 = beta1 + beta2 by
    unfold quadraticMixing; ring]
  rw [show linearMixing beta1 beta2 beta1 = 2 * (beta1 + beta2) by
    unfold linearMixing; ring]
  field_simp [hSum]

theorem pt_cubic_mixing_positive
    (beta1 beta2 : ℝ) (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2) :
    0 < linearMixing beta1 beta2 beta1 ∧
      0 < quadraticMixing beta2 beta1 := by
  unfold linearMixing quadraticMixing
  constructor <;> nlinarith

end P0EFTJanusLambda3BetaCombination
end JanusFormal

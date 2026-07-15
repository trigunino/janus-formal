import Mathlib

namespace JanusFormal
namespace P0EFTJanusCanonicalVainshteinCoefficient

set_option autoImplicit false

noncomputable section

def plusC2 (s : ℝ) : ℝ := s ^ 2 / 2
def plusC3 (s : ℝ) : ℝ := s ^ 2
def minusC2 (q2 s : ℝ) : ℝ := q2 * s ^ 2 / 2
def minusC3Rho (q2 s : ℝ) : ℝ := q2 * s ^ 2
def dualC3 (c2 c3 : ℝ) : ℝ := 2 * c2 - c3

theorem pt_minus_cubic_cancels (q2 s : ℝ) :
    dualC3 (minusC2 q2 s) (minusC3Rho q2 s) = 0 := by
  unfold dualC3 minusC2 minusC3Rho
  ring

theorem pt_combined_coefficients (q2 s : ℝ) :
    plusC2 s + minusC2 q2 s = s ^ 2 * (1 + q2) / 2 ∧
      plusC3 s + dualC3 (minusC2 q2 s) (minusC3Rho q2 s) = s ^ 2 := by
  unfold plusC2 plusC3 minusC2 minusC3Rho dualC3
  constructor <;> ring

end
end P0EFTJanusCanonicalVainshteinCoefficient
end JanusFormal

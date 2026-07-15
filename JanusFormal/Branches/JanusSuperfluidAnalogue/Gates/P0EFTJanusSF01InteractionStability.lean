import Mathlib

namespace JanusFormal
namespace P0EFTJanusSF01InteractionStability

set_option autoImplicit false

noncomputable section

/-- Symmetric two-condensate homogeneous interaction energy. -/
def interactionEnergy (g g12 n1 n2 : ℝ) : ℝ :=
  g * (n1 ^ 2 + n2 ^ 2) / 2 + g12 * n1 * n2

/-- Exact common/relative density decomposition. -/
theorem interaction_energy_mode_decomposition
    (g g12 n1 n2 : ℝ) :
    4 * interactionEnergy g g12 n1 n2 =
      (g + g12) * (n1 + n2) ^ 2 +
      (g - g12) * (n1 - n2) ^ 2 := by
  unfold interactionEnergy
  ring

theorem stable_couplings_give_nonnegative_interaction
    (g g12 n1 n2 : ℝ)
    (hCommon : 0 ≤ g + g12) (hRelative : 0 ≤ g - g12) :
    0 ≤ interactionEnergy g g12 n1 n2 := by
  have hModes :
      0 ≤ (g + g12) * (n1 + n2) ^ 2 +
        (g - g12) * (n1 - n2) ^ 2 := by positivity
  rw [← interaction_energy_mode_decomposition] at hModes
  linarith

end

end P0EFTJanusSF01InteractionStability
end JanusFormal

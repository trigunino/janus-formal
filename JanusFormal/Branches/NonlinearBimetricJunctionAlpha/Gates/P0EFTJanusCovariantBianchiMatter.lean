import Mathlib

namespace JanusFormal
namespace P0EFTJanusCovariantBianchiMatter

set_option autoImplicit false

def interactionNoetherBalance
    (plusVolume plusDivergence minusVolume minusDivergence : ℝ) : Prop :=
  plusVolume * plusDivergence + minusVolume * minusDivergence = 0

theorem minus_interaction_divergence_fixed
    (plusVolume plusDivergence minusVolume minusDivergence : ℝ)
    (hMinusVolume : minusVolume ≠ 0)
    (hBalance : interactionNoetherBalance
      plusVolume plusDivergence minusVolume minusDivergence) :
    minusDivergence = -(plusVolume / minusVolume) * plusDivergence := by
  unfold interactionNoetherBalance at hBalance
  field_simp [hMinusVolume]
  nlinarith

theorem separate_matter_shell_conservation
    (plusMatterDivergence minusMatterDivergence : ℝ)
    (hPlus : plusMatterDivergence = 0)
    (hMinus : minusMatterDivergence = 0) :
    plusMatterDivergence = 0 ∧ minusMatterDivergence = 0 :=
  ⟨hPlus, hMinus⟩

end P0EFTJanusCovariantBianchiMatter
end JanusFormal

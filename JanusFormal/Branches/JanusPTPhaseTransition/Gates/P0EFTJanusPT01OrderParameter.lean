import Mathlib

namespace JanusFormal
namespace P0EFTJanusPT01OrderParameter

set_option autoImplicit false

/-- Minimal PT-even Landau potential. -/
def landauPotential (a b phi : ℝ) : ℝ :=
  a * phi ^ 2 + b * phi ^ 4

theorem landau_potential_is_pt_even (a b phi : ℝ) :
    landauPotential a b (-phi) = landauPotential a b phi := by
  unfold landauPotential
  ring

/-- PT invariance removes odd monomials in the minimal scalar model, but does
not determine either even coefficient. -/
theorem pt_symmetry_does_not_select_coefficients
    (a1 b1 a2 b2 : ℝ) :
    (∀ phi, landauPotential a1 b1 (-phi) = landauPotential a1 b1 phi) ∧
    (∀ phi, landauPotential a2 b2 (-phi) = landauPotential a2 b2 phi) := by
  exact ⟨landau_potential_is_pt_even a1 b1,
    landau_potential_is_pt_even a2 b2⟩

end P0EFTJanusPT01OrderParameter
end JanusFormal

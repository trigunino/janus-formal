import JanusFormal.Branches.JanusPTPhaseTransition.Gates.P0EFTJanusPT01OrderParameter

namespace JanusFormal
namespace P0EFTJanusPT02LandauMinima

set_option autoImplicit false

open P0EFTJanusPT01OrderParameter

def landauGradient (a b phi : ℝ) : ℝ :=
  2 * a * phi + 4 * b * phi ^ 3

def landauCurvature (a b phi : ℝ) : ℝ :=
  2 * a + 12 * b * phi ^ 2

theorem symmetric_point_is_stationary (a b : ℝ) :
    landauGradient a b 0 = 0 := by
  simp [landauGradient]

theorem nonnegative_quadratic_positive_quartic_selects_zero
    (a b phi : ℝ) (hA : 0 ≤ a) (hB : 0 < b) :
    0 ≤ landauPotential a b phi := by
  unfold landauPotential
  positivity

theorem nonzero_stationary_point_requires_negative_a
    (a b phi : ℝ)
    (hB : 0 < b) (hPhi : phi ≠ 0)
    (hStationary : landauGradient a b phi = 0) :
    a < 0 ∧ phi ^ 2 = -a / (2 * b) := by
  unfold landauGradient at hStationary
  have hRelation : a + 2 * b * phi ^ 2 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hPhi
    nlinarith [hStationary]
  constructor
  · have hPhiSq : 0 < phi ^ 2 := sq_pos_of_ne_zero hPhi
    nlinarith
  · field_simp
    nlinarith

theorem broken_minimum_curvature_is_positive
    (a b phi : ℝ)
    (hA : a < 0)
    (hRelation : phi ^ 2 = -a / (2 * b))
    (hB : b ≠ 0) :
    landauCurvature a b phi = -4 * a ∧
      0 < landauCurvature a b phi := by
  constructor
  · unfold landauCurvature
    rw [hRelation]
    field_simp
    ring
  · have hValue : landauCurvature a b phi = -4 * a := by
      unfold landauCurvature
      rw [hRelation]
      field_simp
      ring
    rw [hValue]
    linarith

end P0EFTJanusPT02LandauMinima
end JanusFormal

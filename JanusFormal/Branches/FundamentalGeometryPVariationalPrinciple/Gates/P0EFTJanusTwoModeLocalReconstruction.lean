import Mathlib

/-!
# Boundary reconstruction inside an oriented two-mode local chain

The bulk operator is the actual real symmetric nearest-neighbor matrix
`[[a,b],[b,c]]`, coupled to the boundary through `g e₀`. Its first four boundary
moments determine all four coefficients when `g > 0` and `b > 0` fix orientation.
The locality class and its orientation are supplied hypotheses; this result does
not derive a Janus physical parent or choose a physical locality class.
-/

namespace JanusFormal
namespace P0EFTJanusTwoModeLocalReconstruction

set_option autoImplicit false
noncomputable section

open Matrix

def bulk (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]

def boundary (g : ℝ) : Fin 2 → ℝ := ![g, 0]

/-- The boundary contraction of an actual matrix power. -/
def moment (a b c g : ℝ) (n : ℕ) : ℝ := g ^ 2 * (bulk a b c ^ n) 0 0

theorem moment_eq_boundary_contraction (a b c g : ℝ) (n : ℕ) :
    moment a b c g n = dotProduct (boundary g) ((bulk a b c ^ n) *ᵥ boundary g) := by
  simp [moment, boundary, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem bulk_symmetric (a b c : ℝ) : (bulk a b c).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem moment_zero (a b c g : ℝ) : moment a b c g 0 = g ^ 2 := by
  simp [moment]

@[simp] theorem moment_one (a b c g : ℝ) : moment a b c g 1 = g ^ 2 * a := by
  simp [moment, bulk]

theorem moment_two (a b c g : ℝ) :
    moment a b c g 2 = g ^ 2 * (a ^ 2 + b ^ 2) := by
  norm_num [moment, bulk, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem moment_three (a b c g : ℝ) :
    moment a b c g 3 = g ^ 2 * (a ^ 3 + 2 * a * b ^ 2 + b ^ 2 * c) := by
  norm_num [moment, bulk, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp

/-- Four moments reconstruct the chain once both coupling signs are fixed. -/
theorem first_four_moments_injective
    (a b c g a' b' c' g' : ℝ)
    (hb : 0 < b) (hg : 0 < g) (hb' : 0 < b') (hg' : 0 < g')
    (h : ∀ n : Fin 4, moment a b c g n = moment a' b' c' g' n) :
    a = a' ∧ b = b' ∧ c = c' ∧ g = g' := by
  have h0 : g ^ 2 = g' ^ 2 := by simpa using h 0
  have heqg : g = g' := (sq_eq_sq₀ hg.le hg'.le).mp h0
  subst g'
  have h1 : g ^ 2 * a = g ^ 2 * a' := by simpa using h 1
  have heqa : a = a' := mul_left_cancel₀ (pow_ne_zero 2 hg.ne') h1
  subst a'
  have h2 : a ^ 2 + b ^ 2 = a ^ 2 + b' ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 2 hg.ne') (by simpa [moment_two] using h 2)
  have heqb : b = b' := (sq_eq_sq₀ hb.le hb'.le).mp (by linarith)
  subst b'
  have h3 : a ^ 3 + 2 * a * b ^ 2 + b ^ 2 * c =
      a ^ 3 + 2 * a * b ^ 2 + b ^ 2 * c' :=
    mul_left_cancel₀ (pow_ne_zero 2 hg.ne') (by simpa [moment_three] using h 3)
  have heqc : c = c' := mul_left_cancel₀ (pow_ne_zero 2 hb.ne') (by linarith)
  exact ⟨rfl, rfl, heqc, rfl⟩

/-- Columns are precisely the coupled vector `B` and its first bulk iterate `AB`. -/
def krylovMatrix (a b c g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![boundary g 0, (bulk a b c *ᵥ boundary g) 0;
     boundary g 1, (bulk a b c *ᵥ boundary g) 1]

theorem krylovMatrix_det (a b c g : ℝ) :
    (krylovMatrix a b c g).det = b * g ^ 2 := by
  simp [krylovMatrix, boundary, bulk, Matrix.det_fin_two,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Nonzero determinant certifies that no second bulk mode is invisible. -/
theorem krylovMatrix_det_pos (a b c g : ℝ) (hb : 0 < b) (hg : 0 < g) :
    0 < (krylovMatrix a b c g).det := by
  rw [krylovMatrix_det]
  positivity

/-- With the link removed, every boundary moment loses the second diagonal. -/
theorem moment_uncoupled (a c g : ℝ) (n : ℕ) :
    moment a 0 c g n = g ^ 2 * a ^ n := by
  have hp : ∀ k : ℕ, (bulk a 0 c ^ k) 0 0 = a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      change (bulk a 0 c ^ k) 0 0 * a + (bulk a 0 c ^ k) 0 1 * 0 = a ^ (k + 1)
      simp [ih, pow_succ]
  simp [moment, hp]

theorem uncoupled_invisible_diagonal (a c c' g : ℝ) (n : ℕ) :
    moment a 0 c g n = moment a 0 c' g n := by
  rw [moment_uncoupled, moment_uncoupled]

end
end P0EFTJanusTwoModeLocalReconstruction
end JanusFormal

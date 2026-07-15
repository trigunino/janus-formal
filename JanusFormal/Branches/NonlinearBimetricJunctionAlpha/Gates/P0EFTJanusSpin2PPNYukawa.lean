import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpin2PPNYukawa

set_option autoImplicit false

noncomputable def phiFactor (alpha yukawa : ℝ) : ℝ :=
  1 + (4 / 3 : ℝ) * alpha * yukawa

noncomputable def psiFactor (alpha yukawa : ℝ) : ℝ :=
  1 + (2 / 3 : ℝ) * alpha * yukawa

noncomputable def gammaPPN (alpha yukawa : ℝ) : ℝ :=
  psiFactor alpha yukawa / phiFactor alpha yukawa

theorem gammaPPN_formula
    (alpha yukawa : ℝ) (_hDen : 3 + 4 * alpha * yukawa ≠ 0) :
    gammaPPN alpha yukawa =
      (3 + 2 * alpha * yukawa) / (3 + 4 * alpha * yukawa) := by
  unfold gammaPPN phiFactor psiFactor
  field_simp

theorem equal_kinetic_unsuppressed_gamma :
    gammaPPN 1 1 = 5 / 7 := by
  norm_num [gammaPPN, phiFactor, psiFactor]

theorem cross_short_distance_factors :
    phiFactor (-1) 1 = -1 / 3 ∧ psiFactor (-1) 1 = 1 / 3 := by
  constructor <;> norm_num [phiFactor, psiFactor]

theorem cross_short_distance_not_decoupled :
    ¬ (phiFactor (-1) 1 = 0 ∧ psiFactor (-1) 1 = 0) := by
  norm_num [phiFactor, psiFactor]

end P0EFTJanusSpin2PPNYukawa
end JanusFormal

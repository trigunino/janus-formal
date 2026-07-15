import Mathlib

namespace JanusFormal.P0EFTJanusBackgroundVertexExpansion

set_option autoImplicit false

noncomputable def inverseSquareTruncation (v eta : ℝ) : ℝ :=
  1 / v ^ 2 - 2 * eta / v ^ 3 + 3 * eta ^ 2 / v ^ 4

noncomputable def inverseSquareRemainder (v eta : ℝ) : ℝ :=
  -(eta ^ 3 * (3 * eta + 4 * v)) /
    (v ^ 4 * (eta + v) ^ 2)

/-- Exact second-order background expansion with its untruncated remainder. -/
theorem inverse_square_expansion_exact
    (v eta : ℝ) (hV : v ≠ 0) (hBackground : eta + v ≠ 0) :
    1 / (eta + v) ^ 2 =
      inverseSquareTruncation v eta + inverseSquareRemainder v eta := by
  unfold inverseSquareTruncation inverseSquareRemainder
  field_simp [hV, hBackground, pow_ne_zero]
  ring

/-- The quadratic vertex coefficients are fixed by the inverse-square
dressing; they are not independent counterterm parameters. -/
structure BackgroundVertexCoefficients where
  condensate : ℝ
  maxwell : ℝ
  scalarMaxwell : ℝ
  scalarSquaredMaxwell : ℝ
  condensateNonzero : condensate ≠ 0
  maxwellLaw : maxwell = 1 / condensate ^ 2
  scalarMaxwellLaw : scalarMaxwell = -2 / condensate ^ 3
  scalarSquaredMaxwellLaw : scalarSquaredMaxwell = 3 / condensate ^ 4

theorem vertex_ratio_lock (s : BackgroundVertexCoefficients) :
    s.scalarMaxwell ^ 2 =
      (4 / 3 : ℝ) * s.maxwell * s.scalarSquaredMaxwell := by
  rw [s.maxwellLaw, s.scalarMaxwellLaw, s.scalarSquaredMaxwellLaw]
  field_simp [s.condensateNonzero]
  ring

end JanusFormal.P0EFTJanusBackgroundVertexExpansion

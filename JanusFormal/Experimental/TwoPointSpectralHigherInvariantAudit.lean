import JanusFormal.Experimental.TwoPointSpectralNonlinearBimetricAudit

/-!
# Higher-invariant audit for the two-point spectral seed

The natural even spectral extension through quartic order is tested against
the exact PT-flat proportional interaction.  This remains isolated from every
supported Janus program head.
-/

namespace JanusFormal
namespace ExperimentalTwoPointSpectralHigherInvariantAudit

set_option autoImplicit false

/-- Most general even reduced spectral polynomial through fourth order. -/
def evenSpectralQuartic
    (quadratic quartic displacement : ℝ) : ℝ :=
  quadratic * displacement ^ 2 + quartic * displacement ^ 4

/-- The PT-flat target written in the displacement `c = 1 + x`. -/
def ptDisplacementTarget
    (beta1 beta2 displacement : ℝ) : ℝ :=
  12 * (beta1 + beta2) * displacement ^ 2 +
  12 * (beta1 + beta2) * displacement ^ 3 +
  (4 * beta1 + 3 * beta2) * displacement ^ 4

/-- Every even quartic spectral extension has zero odd part. -/
theorem even_spectral_quartic_has_zero_odd_part
    (quadratic quartic x : ℝ) :
    evenSpectralQuartic quadratic quartic x -
      evenSpectralQuartic quadratic quartic (-x) = 0 := by
  unfold evenSpectralQuartic
  ring

/-- The odd part of the bimetric target is precisely its cubic interaction. -/
theorem pt_target_odd_part
    (beta1 beta2 x : ℝ) :
    ptDisplacementTarget beta1 beta2 x -
      ptDisplacementTarget beta1 beta2 (-x) =
        24 * (beta1 + beta2) * x ^ 3 := by
  unfold ptDisplacementTarget
  ring

/-- Exact matching by even quadratic/quartic invariants forces the cubic
coefficient, and hence the PT-flat Fierz--Pauli combination, to vanish. -/
theorem even_higher_invariants_force_zero_fp_combination
    (quadratic quartic beta1 beta2 : ℝ)
    (hGlobal : ∀ x : ℝ,
      evenSpectralQuartic quadratic quartic x =
        ptDisplacementTarget beta1 beta2 x) :
    beta1 + beta2 = 0 := by
  have hPlus := hGlobal 1
  have hMinus := hGlobal (-1)
  unfold evenSpectralQuartic ptDisplacementTarget at hPlus hMinus
  norm_num at hPlus hMinus
  linarith

/-- Therefore no such extension matches the physically selected cone
`beta1 > 0`, `beta2 >= 0`. -/
theorem even_higher_invariants_no_go_on_safe_cone
    (quadratic quartic beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2) :
    ¬ (∀ x : ℝ,
      evenSpectralQuartic quadratic quartic x =
        ptDisplacementTarget beta1 beta2 x) := by
  intro hGlobal
  have hZero := even_higher_invariants_force_zero_fp_combination
    quadratic quartic beta1 beta2 hGlobal
  linarith

/-- If the forbidden zero-FP branch is allowed, coefficient matching reduces
to a pure quartic interaction; this records the degenerate escape explicitly. -/
theorem zero_fp_degenerate_match
    (beta1 beta2 : ℝ)
    (hZero : beta1 + beta2 = 0) :
    ∀ x : ℝ,
      evenSpectralQuartic 0 (4 * beta1 + 3 * beta2) x =
        ptDisplacementTarget beta1 beta2 x := by
  intro x
  unfold evenSpectralQuartic ptDisplacementTarget
  rw [hZero]
  ring

end ExperimentalTwoPointSpectralHigherInvariantAudit
end JanusFormal

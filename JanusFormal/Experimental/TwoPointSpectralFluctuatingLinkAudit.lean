import JanusFormal.Experimental.TwoPointSpectralHigherInvariantAudit

/-!
# Affine fluctuating-link audit

This isolated experiment tests the smallest field-dependent link capable of
producing a cubic term from the two-point spectral action.
-/

namespace JanusFormal
namespace ExperimentalTwoPointSpectralFluctuatingLinkAudit

set_option autoImplicit false

open ExperimentalTwoPointSpectralHigherInvariantAudit

/-- Spectral action with affine fluctuated link `m(x) = m0 * (1 + a*x)`. -/
def affineLinkAction
    (baseLink slope displacement : ℝ) : ℝ :=
  (baseLink * (1 + slope * displacement)) ^ 2 * displacement ^ 2

/-- Exact quadratic/cubic/quartic expansion of the affine-link action. -/
theorem affine_link_expansion
    (baseLink slope x : ℝ) :
    affineLinkAction baseLink slope x =
      baseLink ^ 2 * x ^ 2 +
      2 * slope * baseLink ^ 2 * x ^ 3 +
      slope ^ 2 * baseLink ^ 2 * x ^ 4 := by
  unfold affineLinkAction
  ring

/-- Matching the quadratic and cubic PT coefficients fixes the link slope to
`1/2` whenever the massive coefficient is nonzero. -/
theorem quadratic_cubic_matching_fixes_half_slope
    (baseLink slope beta1 beta2 : ℝ)
    (hMass : baseLink ^ 2 = 12 * (beta1 + beta2))
    (hCubic : 2 * slope * baseLink ^ 2 = 12 * (beta1 + beta2))
    (hNonzero : beta1 + beta2 ≠ 0) :
    slope = (1 : ℝ) / 2 := by
  rw [hMass] at hCubic
  apply (mul_left_cancel₀ hNonzero)
  nlinarith

/-- Matching all three PT coefficients with one affine link forces `beta1=0`.
Thus the affine completion misses the selected cone, where `beta1>0`. -/
theorem affine_link_coefficient_match_forces_beta1_zero
    (baseLink slope beta1 beta2 : ℝ)
    (hQuadratic : baseLink ^ 2 = 12 * (beta1 + beta2))
    (hCubic : 2 * slope * baseLink ^ 2 = 12 * (beta1 + beta2))
    (hQuartic : slope ^ 2 * baseLink ^ 2 = 4 * beta1 + 3 * beta2)
    (hNonzero : beta1 + beta2 ≠ 0) :
    beta1 = 0 := by
  have hSlope := quadratic_cubic_matching_fixes_half_slope
    baseLink slope beta1 beta2 hQuadratic hCubic hNonzero
  rw [hSlope, hQuadratic] at hQuartic
  norm_num at hQuartic
  linarith

/-- No affine fluctuating link reproduces the PT target on the safe cone. -/
theorem affine_link_no_go_on_safe_cone
    (baseLink slope beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2) :
    ¬ (∀ x : ℝ,
      affineLinkAction baseLink slope x =
        ptDisplacementTarget beta1 beta2 x) := by
  intro hGlobal
  have h1 := hGlobal 1
  have hNeg1 := hGlobal (-1)
  have h2 := hGlobal 2
  unfold affineLinkAction ptDisplacementTarget at h1 hNeg1 h2
  norm_num at h1 hNeg1 h2
  nlinarith [sq_nonneg baseLink, sq_nonneg slope]

end ExperimentalTwoPointSpectralFluctuatingLinkAudit
end JanusFormal

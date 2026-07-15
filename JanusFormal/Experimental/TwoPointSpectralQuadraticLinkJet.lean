import JanusFormal.Experimental.TwoPointSpectralFluctuatingLinkAudit

/-!
# Quadratic fluctuating-link finite-jet bridge

This isolated experiment matches the PT-flat interaction through fourth order
and records the exact fifth- and sixth-order obstruction.
-/

namespace JanusFormal
namespace ExperimentalTwoPointSpectralQuadraticLinkJet

set_option autoImplicit false

open ExperimentalTwoPointSpectralHigherInvariantAudit

/-- Reduced action for `m(x) = m0 * (1 + a*x + b*x^2)`, expressed using
`m0^2` so no square-root choice is required. -/
def quadraticLinkAction
    (baseSquared slope curvature displacement : ℝ) : ℝ :=
  baseSquared *
    (1 + slope * displacement + curvature * displacement ^ 2) ^ 2 *
    displacement ^ 2

/-- Parameters uniquely suggested by coefficient matching through order four. -/
noncomputable def matchedBaseSquared (beta1 beta2 : ℝ) : ℝ :=
  12 * (beta1 + beta2)

noncomputable def matchedSlope : ℝ := (1 : ℝ) / 2

noncomputable def matchedCurvature (beta1 beta2 : ℝ) : ℝ :=
  beta1 / (24 * (beta1 + beta2))

/-- Exact result: the quadratic fluctuating link matches B through degree four;
the remaining discrepancy starts at degree five. -/
theorem quadratic_link_exact_residual
    (beta1 beta2 x : ℝ)
    (hNonzero : beta1 + beta2 ≠ 0) :
    quadraticLinkAction
        (matchedBaseSquared beta1 beta2)
        matchedSlope
        (matchedCurvature beta1 beta2) x =
      ptDisplacementTarget beta1 beta2 x +
        (beta1 / 2) * x ^ 5 +
        (beta1 ^ 2 / (48 * (beta1 + beta2))) * x ^ 6 := by
  unfold quadraticLinkAction matchedBaseSquared matchedSlope matchedCurvature
    ptDisplacementTarget
  field_simp [hNonzero]
  ring

/-- The fourth-order jet is therefore exactly the PT-flat target jet. -/
theorem fourth_order_jet_matches
    (beta1 beta2 : ℝ)
    (hNonzero : beta1 + beta2 ≠ 0) :
    ∃ fifth sixth : ℝ,
      ∀ x : ℝ,
        quadraticLinkAction
            (matchedBaseSquared beta1 beta2)
            matchedSlope
            (matchedCurvature beta1 beta2) x =
          ptDisplacementTarget beta1 beta2 x +
            fifth * x ^ 5 + sixth * x ^ 6 := by
  refine ⟨beta1 / 2, beta1 ^ 2 / (48 * (beta1 + beta2)), ?_⟩
  intro x
  exact quadratic_link_exact_residual beta1 beta2 x hNonzero

/-- On the safe cone the first unaccounted coefficient is strictly positive,
so the fourth-order jet match is not an exact global completion. -/
theorem safe_cone_has_nonzero_fifth_order_obstruction
    (beta1 : ℝ)
    (hBeta1 : 0 < beta1) :
    0 < beta1 / 2 := by
  positivity

/-- Matching the quadratic and cubic coefficients fixes the base coefficient
and slope, while matching the quartic coefficient fixes the curvature. -/
theorem fourth_order_matching_fixes_parameters
    (baseSquared slope curvature beta1 beta2 : ℝ)
    (hQuadratic : baseSquared = 12 * (beta1 + beta2))
    (hCubic : 2 * slope * baseSquared = 12 * (beta1 + beta2))
    (hQuartic : (slope ^ 2 + 2 * curvature) * baseSquared =
      4 * beta1 + 3 * beta2)
    (hNonzero : beta1 + beta2 ≠ 0) :
    baseSquared = matchedBaseSquared beta1 beta2 ∧
      slope = matchedSlope ∧
      curvature = matchedCurvature beta1 beta2 := by
  have hSlope : slope = (1 : ℝ) / 2 := by
    rw [hQuadratic] at hCubic
    apply (mul_left_cancel₀ hNonzero)
    nlinarith
  constructor
  · exact hQuadratic
  constructor
  · exact hSlope
  · rw [hSlope, hQuadratic] at hQuartic
    unfold matchedCurvature
    field_simp [hNonzero]
    field_simp [hNonzero] at hQuartic
    linarith

end ExperimentalTwoPointSpectralQuadraticLinkJet
end JanusFormal

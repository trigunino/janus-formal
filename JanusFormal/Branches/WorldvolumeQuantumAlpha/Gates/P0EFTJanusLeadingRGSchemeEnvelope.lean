import Mathlib

namespace JanusFormal.P0EFTJanusLeadingRGSchemeEnvelope

set_option autoImplicit false

noncomputable section

/-!
Leading-order scheme and uncertainty envelope for the conditional 2+1D
world-volume candidate.  Unknown gauge/LL residues remain explicit.
-/

/-- Under `lambda' = lambda + a lambda^2`, the chain-rule transformed beta
keeps the same quadratic coefficient; the change starts cubically. -/
theorem quadratic_beta_coefficient_finite_redefinition_invariant
    (lambda a beta₂ : ℝ) :
    (1 + 2 * a * lambda) * (beta₂ * lambda ^ 2) =
      beta₂ * lambda ^ 2 + 2 * a * beta₂ * lambda ^ 3 := by
  ring

structure LeadingRGEnvelope where
  lambda6 : ℝ
  gammaSigma : ℝ
  unresolvedBeta : ℝ
  gammaUpper : ℝ
  unresolvedBetaLower : ℝ
  lambdaPositive : 0 < lambda6
  gammaBound : gammaSigma ≤ gammaUpper
  unresolvedBetaBound : unresolvedBetaLower ≤ unresolvedBeta

def pureScalarBeta (s : LeadingRGEnvelope) : ℝ :=
  (25 / (2 * Real.pi ^ 2)) * s.lambda6 ^ 2

def totalLogCoefficient (s : LeadingRGEnvelope) : ℝ :=
  pureScalarBeta s + s.unresolvedBeta - 3 * s.gammaSigma * s.lambda6

/-- A regulator-independent sufficient condition that keeps the unresolved
gauge and LL beta contribution as a certified lower bound. -/
theorem total_log_positive_from_envelope
    (s : LeadingRGEnvelope)
    (hMargin :
      3 * s.gammaUpper * s.lambda6 <
        pureScalarBeta s + s.unresolvedBetaLower) :
    0 < totalLogCoefficient s := by
  unfold totalLogCoefficient
  have hGammaMul :
      3 * s.gammaSigma * s.lambda6 ≤
        3 * s.gammaUpper * s.lambda6 := by
    nlinarith [s.lambdaPositive, s.gammaBound]
  linarith [s.unresolvedBetaBound]

/-- In particular, nonnegative unresolved beta corrections preserve the
pure-scalar sign whenever the anomalous term stays below it. -/
theorem nonnegative_unresolved_sector_preserves_stability
    (s : LeadingRGEnvelope)
    (hUnresolved : 0 ≤ s.unresolvedBetaLower)
    (hGamma : 3 * s.gammaUpper * s.lambda6 < pureScalarBeta s) :
    0 < totalLogCoefficient s := by
  apply total_log_positive_from_envelope s
  linarith

end

end JanusFormal.P0EFTJanusLeadingRGSchemeEnvelope

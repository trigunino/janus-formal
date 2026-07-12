import Mathlib
import JanusFormal.Branches.AlphaDeepCompletion.Gates.P0EFTJanusDiscreteMicroscopicAlphaCandidate

namespace JanusFormal
namespace P0EFTJanusQuadraticBetaDiscreteClosure

set_option autoImplicit false

open P0EFTJanusDiscreteMicroscopicAlphaCandidate

/--
A leading nonzero sextic beta law

`beta6 = b0 * lambda6^2`

attached to the discrete microscopic Janus candidate.
-/
structure QuadraticBetaMatchedAlpha extends MatchedMicroscopicAlpha where
  betaCoefficient : ℝ
  betaCoefficientPositive : 0 < betaCoefficient
  sexticCouplingNonzero : oneLog.sexticCoupling ≠ 0
  quadraticBetaLaw :
    oneLog.betaSextic =
      betaCoefficient * oneLog.sexticCoupling ^ 2

/-- Dimensionless denominator selected by the integer level. -/
def discreteDenominator (s : QuadraticBetaMatchedAlpha) : ℝ :=
  24 * Real.pi ^ 2 * (s.levelLocked.chernSimonsLevel : ℝ) -
    s.levelLocked.lockConstant

/--
The discrete consistency relation cancels one nonzero power of `lambda6` and
fixes the coupling linearly:

`b0 * D * lambda6 = 3*C`.
-/
theorem quadratic_beta_fixes_sextic_coupling
    (s : QuadraticBetaMatchedAlpha) :
    s.betaCoefficient * discreteDenominator s *
        s.oneLog.sexticCoupling =
      3 * s.levelLocked.lockConstant := by
  have hDiscrete :=
    discrete_level_selects_sextic_coupling s.toMatchedMicroscopicAlpha
  rw [s.quadraticBetaLaw] at hDiscrete
  have hFactor :
      s.oneLog.sexticCoupling *
        (s.betaCoefficient * discreteDenominator s *
            s.oneLog.sexticCoupling -
          3 * s.levelLocked.lockConstant) = 0 := by
    unfold discreteDenominator
    nlinarith [hDiscrete]
  have hBracket :
      s.betaCoefficient * discreteDenominator s *
          s.oneLog.sexticCoupling -
        3 * s.levelLocked.lockConstant = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left s.sexticCouplingNonzero
  linarith

/-- Positive denominator implies a positive selected sextic coupling. -/
theorem selected_sextic_coupling_positive
    (s : QuadraticBetaMatchedAlpha)
    (hDenominator : 0 < discreteDenominator s) :
    0 < s.oneLog.sexticCoupling := by
  have hEquation := quadratic_beta_fixes_sextic_coupling s
  have hLeftCoefficient :
      0 < s.betaCoefficient * discreteDenominator s :=
    mul_pos s.betaCoefficientPositive hDenominator
  have hRight : 0 < 3 * s.levelLocked.lockConstant :=
    mul_pos (by norm_num) s.levelLocked.lockConstantPositive
  nlinarith

/-- The same `b0`, level and lock constant select the same sextic coupling. -/
theorem same_quadratic_beta_data_fix_sextic_coupling
    (s₁ s₂ : QuadraticBetaMatchedAlpha)
    (hB0 : s₁.betaCoefficient = s₂.betaCoefficient)
    (hLevel :
      s₁.levelLocked.chernSimonsLevel =
        s₂.levelLocked.chernSimonsLevel)
    (hLock :
      s₁.levelLocked.lockConstant = s₂.levelLocked.lockConstant)
    (hDenominator : 0 < discreteDenominator s₂) :
    s₁.oneLog.sexticCoupling = s₂.oneLog.sexticCoupling := by
  have h₁ := quadratic_beta_fixes_sextic_coupling s₁
  have h₂ := quadratic_beta_fixes_sextic_coupling s₂
  have hDenominatorEq : discreteDenominator s₁ = discreteDenominator s₂ := by
    unfold discreteDenominator
    rw [hLevel, hLock]
  rw [hB0, hDenominatorEq, hLock] at h₁
  have hCoefficient :
      0 < s₂.betaCoefficient * discreteDenominator s₂ :=
    mul_pos s₂.betaCoefficientPositive hDenominator
  nlinarith [h₁, h₂]

/--
With a positive quadratic beta coefficient, positive denominator and a fixed UV
anchor, the integer level determines one absolute Janus length.
-/
theorem same_quadratic_beta_theory_fixes_alpha
    (s₁ s₂ : QuadraticBetaMatchedAlpha)
    (hUV :
      s₁.levelLocked.uvLength = s₂.levelLocked.uvLength)
    (hB0 : s₁.betaCoefficient = s₂.betaCoefficient)
    (hLevel :
      s₁.levelLocked.chernSimonsLevel =
        s₂.levelLocked.chernSimonsLevel)
    (hLock :
      s₁.levelLocked.lockConstant = s₂.levelLocked.lockConstant)
    (hDenominator : 0 < discreteDenominator s₂) :
    s₁.oneLog.alphaSquaredLength =
      s₂.oneLog.alphaSquaredLength := by
  exact same_discrete_theory_fixes_same_alpha
    s₁.toMatchedMicroscopicAlpha s₂.toMatchedMicroscopicAlpha
    hUV hLevel
    (by
      have hLambda := same_quadratic_beta_data_fix_sextic_coupling
        s₁ s₂ hB0 hLevel hLock hDenominator
      calc
        s₁.oneLog.betaSextic =
            s₁.betaCoefficient * s₁.oneLog.sexticCoupling ^ 2 :=
          s₁.quadraticBetaLaw
        _ = s₂.betaCoefficient * s₂.oneLog.sexticCoupling ^ 2 := by
          rw [hB0, hLambda]
        _ = s₂.oneLog.betaSextic := s₂.quadraticBetaLaw.symm)
    hLock

/-- Primitive level `k=1` reduces the coupling law to one explicit equation. -/
theorem primitive_level_coupling_equation
    (s : QuadraticBetaMatchedAlpha)
    (hLevel : s.levelLocked.chernSimonsLevel = 1) :
    s.betaCoefficient *
        (24 * Real.pi ^ 2 - s.levelLocked.lockConstant) *
        s.oneLog.sexticCoupling =
      3 * s.levelLocked.lockConstant := by
  have h := quadratic_beta_fixes_sextic_coupling s
  unfold discreteDenominator at h
  rw [hLevel] at h
  norm_num at h
  exact h

/--
The remaining physics is now finite and explicit: compute `b0` and `C`, prove
`24*pi^2*k > C`, select the anomaly-allowed integer `k`, and derive the UV
anchor. No continuous sextic fit remains.
-/
structure QuadraticBetaClosureStatus where
  exactOrControlledBetaFunctionComputed : Prop
  positiveLeadingBetaCoefficientProved : Prop
  discreteLockConstantComputed : Prop
  anomalyAllowedLevelSelected : Prop
  positiveDenominatorProved : Prop
  nonzeroSexticBranchSelected : Prop
  uvAnchorDerived : Prop
  chargeNormalizationDerived : Prop
  absoluteAlphaDerivedNoFit : Prop


def quadraticBetaClosure (s : QuadraticBetaClosureStatus) : Prop :=
  s.exactOrControlledBetaFunctionComputed /\
  s.positiveLeadingBetaCoefficientProved /\
  s.discreteLockConstantComputed /\
  s.anomalyAllowedLevelSelected /\
  s.positiveDenominatorProved /\
  s.nonzeroSexticBranchSelected /\
  s.uvAnchorDerived /\
  s.chargeNormalizationDerived /\
  s.absoluteAlphaDerivedNoFit

end P0EFTJanusQuadraticBetaDiscreteClosure
end JanusFormal

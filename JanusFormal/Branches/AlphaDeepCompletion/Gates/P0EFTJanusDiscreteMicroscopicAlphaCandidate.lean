import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusRGConsistentOneLogAlpha
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusChernSimonsLevelLockedAlpha

namespace JanusFormal
namespace P0EFTJanusDiscreteMicroscopicAlphaCandidate

set_option autoImplicit false

open P0EFTJanusRGConsistentOneLogAlpha
open P0EFTJanusChernSimonsLevelLockedAlpha
open P0EFTJanusWorldvolumeRGTransmutation

/--
The one-log composite vacuum and the level-locked transmutation describe the
same positive Janus length. The subtraction mass and UV length are reciprocal,
and the charge amplitude is normalized to one.
-/
structure MatchedMicroscopicAlpha where
  oneLog : RGConsistentOneLogAlpha
  levelLocked : LevelLockedRGScale
  sameAlpha :
    oneLog.alphaSquaredLength = levelLocked.alphaSquaredLength
  reciprocalUVAnchor :
    oneLog.renormalizationMass * levelLocked.uvLength = 1
  unitChargeAmplitude :
    oneLog.chargeAmplitude = 1

/-- Matching both descriptions forces the two hierarchy exponents to cancel. -/
theorem logarithmic_and_rg_exponents_are_opposite
    (s : MatchedMicroscopicAlpha) :
    s.oneLog.logRatio + s.levelLocked.hierarchyExponent = 0 := by
  have hOneLog := beta_improved_alpha_equation s.oneLog
  rw [s.unitChargeAmplitude] at hOneLog
  norm_num at hOneLog
  have hRG :=
    planck_anchored_hierarchy_law s.levelLocked.toRGTransmutedLLScale
  rw [← s.sameAlpha] at hRG
  have hCombined :
      (s.oneLog.renormalizationMass * s.levelLocked.uvLength) *
        (Real.exp s.oneLog.logRatio *
          Real.exp s.levelLocked.hierarchyExponent) = 1 := by
    calc
      (s.oneLog.renormalizationMass * s.levelLocked.uvLength) *
          (Real.exp s.oneLog.logRatio *
            Real.exp s.levelLocked.hierarchyExponent) =
        (2 * s.oneLog.renormalizationMass *
          Real.exp s.oneLog.logRatio *
          s.oneLog.alphaSquaredLength) := by
            rw [hRG]
            ring
      _ = 1 := hOneLog
  rw [s.reciprocalUVAnchor] at hCombined
  norm_num at hCombined
  have hExpSum :
      Real.exp
        (s.oneLog.logRatio + s.levelLocked.hierarchyExponent) = 1 := by
    rw [Real.exp_add]
    exact hCombined
  have hExpZero :
      Real.exp
        (s.oneLog.logRatio + s.levelLocked.hierarchyExponent) =
          Real.exp 0 := by
    simpa using hExpSum
  exact Real.exp_injective hExpZero

/-- The matched hierarchy fixes the sextic coupling relative to the beta function. -/
theorem matched_sextic_beta_exponent_equation
    (s : MatchedMicroscopicAlpha) :
    3 * s.oneLog.betaSextic * s.levelLocked.hierarchyExponent =
      3 * s.oneLog.sexticCoupling + s.oneLog.betaSextic := by
  have hStationary := beta_stationarity_equation s.oneLog
  have hOpposite := logarithmic_and_rg_exponents_are_opposite s
  nlinarith

/--
Eliminating the hierarchy exponent yields the discrete microscopic consistency
condition

`C*(3*lambda6 + beta6) = 24*pi^2*beta6*k`.
-/
theorem discrete_microscopic_consistency_equation
    (s : MatchedMicroscopicAlpha) :
    s.levelLocked.lockConstant *
        (3 * s.oneLog.sexticCoupling + s.oneLog.betaSextic) =
      24 * Real.pi ^ 2 * s.oneLog.betaSextic *
        (s.levelLocked.chernSimonsLevel : ℝ) := by
  have hSextic := matched_sextic_beta_exponent_equation s
  have hLevel := level_locked_exponent_equation s.levelLocked
  calc
    s.levelLocked.lockConstant *
        (3 * s.oneLog.sexticCoupling + s.oneLog.betaSextic) =
      s.levelLocked.lockConstant *
        (3 * s.oneLog.betaSextic *
          s.levelLocked.hierarchyExponent) := by rw [hSextic]
    _ = 3 * s.oneLog.betaSextic *
        (s.levelLocked.lockConstant *
          s.levelLocked.hierarchyExponent) := by ring
    _ = 3 * s.oneLog.betaSextic *
        (8 * Real.pi ^ 2 *
          (s.levelLocked.chernSimonsLevel : ℝ)) := by rw [hLevel]
    _ = 24 * Real.pi ^ 2 * s.oneLog.betaSextic *
        (s.levelLocked.chernSimonsLevel : ℝ) := by ring

/-- The discrete consistency equation selects the sextic coupling. -/
theorem discrete_level_selects_sextic_coupling
    (s : MatchedMicroscopicAlpha) :
    3 * s.levelLocked.lockConstant * s.oneLog.sexticCoupling =
      s.oneLog.betaSextic *
        (24 * Real.pi ^ 2 *
          (s.levelLocked.chernSimonsLevel : ℝ) -
          s.levelLocked.lockConstant) := by
  have hDiscrete := discrete_microscopic_consistency_equation s
  nlinarith

/-- Equal discrete microscopic inputs determine the same sextic coupling. -/
theorem same_level_beta_and_lock_fix_sextic_coupling
    (s₁ s₂ : MatchedMicroscopicAlpha)
    (hLevel :
      s₁.levelLocked.chernSimonsLevel =
        s₂.levelLocked.chernSimonsLevel)
    (hBeta : s₁.oneLog.betaSextic = s₂.oneLog.betaSextic)
    (hLock :
      s₁.levelLocked.lockConstant = s₂.levelLocked.lockConstant) :
    s₁.oneLog.sexticCoupling = s₂.oneLog.sexticCoupling := by
  have h₁ := discrete_level_selects_sextic_coupling s₁
  have h₂ := discrete_level_selects_sextic_coupling s₂
  rw [hLevel, hBeta, hLock] at h₁
  have hLockPositive : 0 < s₂.levelLocked.lockConstant :=
    s₂.levelLocked.lockConstantPositive
  nlinarith [h₁, h₂]

/-- Equal UV anchor, level, beta function and lock constant determine one alpha. -/
theorem same_discrete_theory_fixes_same_alpha
    (s₁ s₂ : MatchedMicroscopicAlpha)
    (hUV :
      s₁.levelLocked.uvLength = s₂.levelLocked.uvLength)
    (hLevel :
      s₁.levelLocked.chernSimonsLevel =
        s₂.levelLocked.chernSimonsLevel)
    (hBeta : s₁.oneLog.betaSextic = s₂.oneLog.betaSextic)
    (hLock :
      s₁.levelLocked.lockConstant = s₂.levelLocked.lockConstant) :
    s₁.oneLog.alphaSquaredLength =
      s₂.oneLog.alphaSquaredLength := by
  have hAlpha := same_discrete_microscopic_data_fix_alpha
    s₁.levelLocked s₂.levelLocked hUV hLevel hLock
  calc
    s₁.oneLog.alphaSquaredLength =
        s₁.levelLocked.alphaSquaredLength := s₁.sameAlpha
    _ = s₂.levelLocked.alphaSquaredLength := hAlpha
    _ = s₂.oneLog.alphaSquaredLength := s₂.sameAlpha.symm

/--
This candidate removes the continuous sextic-coupling fit once the matter beta
function, the integer level and the group-theory lock constant are computed.
-/
structure DiscreteMicroscopicClosureStatus where
  oneLogEffectivePotentialDerived : Prop
  betaFunctionComputed : Prop
  compactChernSimonsLevelDerived : Prop
  anomalyAllowedLevelSelected : Prop
  betaLevelLockConstantComputed : Prop
  reciprocalUVAnchorDerived : Prop
  chargeAmplitudeNormalized : Prop
  discreteConsistencyEquationDerived : Prop
  stableVacuumProvedBeyondTruncation : Prop
  absoluteAlphaPredictedNoFit : Prop


def discreteMicroscopicClosure
    (s : DiscreteMicroscopicClosureStatus) : Prop :=
  s.oneLogEffectivePotentialDerived /\
  s.betaFunctionComputed /\
  s.compactChernSimonsLevelDerived /\
  s.anomalyAllowedLevelSelected /\
  s.betaLevelLockConstantComputed /\
  s.reciprocalUVAnchorDerived /\
  s.chargeAmplitudeNormalized /\
  s.discreteConsistencyEquationDerived /\
  s.stableVacuumProvedBeyondTruncation /\
  s.absoluteAlphaPredictedNoFit

end P0EFTJanusDiscreteMicroscopicAlphaCandidate
end JanusFormal

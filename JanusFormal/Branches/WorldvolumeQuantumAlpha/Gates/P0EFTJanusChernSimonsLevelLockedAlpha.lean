import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusWorldvolumeRGTransmutation

namespace JanusFormal
namespace P0EFTJanusChernSimonsLevelLockedAlpha

set_option autoImplicit false

open P0EFTJanusWorldvolumeRGTransmutation

/--
An integer Chern--Simons level locks the otherwise continuous RG product.

The microscopic lock is written without division:

`B * k = C`,

where `B = beta0*g_UV^2`, `k` is a positive integer level and `C` is a
computed dimensionless matter/group-theory constant.
-/
structure LevelLockedRGScale extends RGTransmutedLLScale where
  chernSimonsLevel : ℕ
  lockConstant : ℝ
  levelPositive : 0 < chernSimonsLevel
  lockConstantPositive : 0 < lockConstant
  betaLevelLock :
    betaCouplingProduct * (chernSimonsLevel : ℝ) = lockConstant

/-- The integer level turns the RG exponent into a discrete relation. -/
theorem level_locked_exponent_equation
    (s : LevelLockedRGScale) :
    s.lockConstant * s.hierarchyExponent =
      8 * Real.pi ^ 2 * (s.chernSimonsLevel : ℝ) := by
  calc
    s.lockConstant * s.hierarchyExponent =
        (s.betaCouplingProduct * (s.chernSimonsLevel : ℝ)) *
          s.hierarchyExponent := by rw [s.betaLevelLock]
    _ = (s.chernSimonsLevel : ℝ) *
          (s.betaCouplingProduct * s.hierarchyExponent) := by ring
    _ = (s.chernSimonsLevel : ℝ) * (8 * Real.pi ^ 2) := by
      rw [s.rgExponentLaw]
    _ = 8 * Real.pi ^ 2 * (s.chernSimonsLevel : ℝ) := by ring

/-- Same integer level and lock constant give the same hierarchy exponent. -/
theorem same_level_and_lock_fix_exponent
    (s₁ s₂ : LevelLockedRGScale)
    (hLevel : s₁.chernSimonsLevel = s₂.chernSimonsLevel)
    (hLock : s₁.lockConstant = s₂.lockConstant) :
    s₁.hierarchyExponent = s₂.hierarchyExponent := by
  have h₁ := level_locked_exponent_equation s₁
  have h₂ := level_locked_exponent_equation s₂
  rw [hLevel, hLock] at h₁
  have hNonzero : s₂.lockConstant ≠ 0 :=
    ne_of_gt s₂.lockConstantPositive
  have hFactor :
      s₂.lockConstant *
        (s₁.hierarchyExponent - s₂.hierarchyExponent) = 0 := by
    nlinarith [h₁, h₂]
  have hDifference :
      s₁.hierarchyExponent - s₂.hierarchyExponent = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hNonzero
  linarith

/-- Same UV anchor, level and lock constant select one Janus length. -/
theorem same_discrete_microscopic_data_fix_alpha
    (s₁ s₂ : LevelLockedRGScale)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hLevel : s₁.chernSimonsLevel = s₂.chernSimonsLevel)
    (hLock : s₁.lockConstant = s₂.lockConstant) :
    s₁.alphaSquaredLength = s₂.alphaSquaredLength := by
  have hExponent := same_level_and_lock_fix_exponent s₁ s₂ hLevel hLock
  have h₁ := planck_anchored_hierarchy_law s₁.toRGTransmutedLLScale
  have h₂ := planck_anchored_hierarchy_law s₂.toRGTransmutedLLScale
  rw [hUV, hExponent] at h₁
  linarith

/-- At fixed positive lock constant, a larger integer level gives a larger exponent. -/
theorem larger_level_gives_larger_exponent
    (s₁ s₂ : LevelLockedRGScale)
    (hLock : s₁.lockConstant = s₂.lockConstant)
    (hLevel : s₁.chernSimonsLevel < s₂.chernSimonsLevel) :
    s₁.hierarchyExponent < s₂.hierarchyExponent := by
  have h₁ := level_locked_exponent_equation s₁
  have h₂ := level_locked_exponent_equation s₂
  rw [← hLock] at h₂
  have hPiPositive : 0 < 8 * Real.pi ^ 2 := by positivity
  have hLevelReal :
      (s₁.chernSimonsLevel : ℝ) < (s₂.chernSimonsLevel : ℝ) := by
    exact_mod_cast hLevel
  have hRight :
      8 * Real.pi ^ 2 * (s₁.chernSimonsLevel : ℝ) <
        8 * Real.pi ^ 2 * (s₂.chernSimonsLevel : ℝ) :=
    mul_lt_mul_of_pos_left hLevelReal hPiPositive
  have hLockPositive : 0 < s₁.lockConstant := s₁.lockConstantPositive
  nlinarith [h₁, h₂, hRight]

/-- At fixed UV anchor and lock constant, larger level gives larger alpha. -/
theorem larger_level_gives_larger_alpha
    (s₁ s₂ : LevelLockedRGScale)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hLock : s₁.lockConstant = s₂.lockConstant)
    (hLevel : s₁.chernSimonsLevel < s₂.chernSimonsLevel) :
    s₁.alphaSquaredLength < s₂.alphaSquaredLength := by
  have hExponent := larger_level_gives_larger_exponent s₁ s₂ hLock hLevel
  exact exponent_strictly_orders_alpha
    s₁.toRGTransmutedLLScale s₂.toRGTransmutedLLScale hUV hExponent

/--
The discrete mechanism is predictive only when `C` and the realized integer
level are fixed by anomaly cancellation, bulk inflow or a microscopic duality.
-/
structure LevelLockClosureStatus where
  compactChernSimonsTheoryDerived : Prop
  integerLevelQuantized : Prop
  anomalyAllowedLevelSetComputed : Prop
  realizedLevelSelected : Prop
  matterGroupConstantComputed : Prop
  betaLevelLockDerived : Prop
  uvAnchorDerived : Prop
  noObservedScaleImported : Prop
  discreteAlphaSpectrumDerived : Prop


def levelLockClosure (s : LevelLockClosureStatus) : Prop :=
  s.compactChernSimonsTheoryDerived /\
  s.integerLevelQuantized /\
  s.anomalyAllowedLevelSetComputed /\
  s.realizedLevelSelected /\
  s.matterGroupConstantComputed /\
  s.betaLevelLockDerived /\
  s.uvAnchorDerived /\
  s.noObservedScaleImported /\
  s.discreteAlphaSpectrumDerived

end P0EFTJanusChernSimonsLevelLockedAlpha
end JanusFormal

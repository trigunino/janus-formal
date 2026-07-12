import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusRGInvariantMCSAlpha
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusMCSAmplitudeLock
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusChernSimonsLevelLockedAlpha

namespace JanusFormal
namespace P0EFTJanusCorrectedDiscreteMCSMatching

set_option autoImplicit false

open P0EFTJanusRGInvariantMCSAlpha
open P0EFTJanusMaxwellChernSimonsChargeNormalization
open P0EFTJanusChernSimonsLevelLockedAlpha
open P0EFTJanusWorldvolumeRGTransmutation

/--
Match the RG-improved MCS vacuum to the level-locked UV transmutation branch.
The same integer Chern--Simons level controls both descriptions.
-/
structure CorrectedDiscreteMCSMatching where
  quantum : RGInvariantMCSAlpha
  levelLocked : LevelLockedRGScale
  sameAlpha :
    quantum.vacuum.alphaSquaredLength =
      levelLocked.alphaSquaredLength
  reciprocalUVAnchor :
    quantum.vacuum.renormalizationMass *
      levelLocked.uvLength = 1
  sameLevel :
    quantum.mcsScale.levelMagnitude =
      (levelLocked.chernSimonsLevel : ℝ)

/--
The properly normalized exponent matching is

`K * exp(x_* + X) = 2*pi`,

not `x_* + X = 0` unless the charge amplitude has been set inconsistently.
-/
theorem corrected_exponent_matching
    (s : CorrectedDiscreteMCSMatching) :
    (s.levelLocked.chernSimonsLevel : ℝ) *
        Real.exp
          (s.quantum.vacuum.logRatio +
            s.levelLocked.hierarchyExponent) =
      2 * Real.pi := by
  have hMCS := level_condensate_alpha_law s.quantum.mcsScale
  rw [s.quantum.sameCondensate, s.quantum.sameAlpha] at hMCS
  rw [s.quantum.vacuum.condensateLaw] at hMCS
  have hRG :=
    planck_anchored_hierarchy_law
      s.levelLocked.toRGTransmutedLLScale
  rw [← s.sameAlpha] at hRG
  have hProduct :
      s.quantum.mcsScale.levelMagnitude *
        (s.quantum.vacuum.renormalizationMass *
          s.levelLocked.uvLength) *
        (Real.exp s.quantum.vacuum.logRatio *
          Real.exp s.levelLocked.hierarchyExponent) =
        2 * Real.pi := by
    calc
      s.quantum.mcsScale.levelMagnitude *
          (s.quantum.vacuum.renormalizationMass *
            s.levelLocked.uvLength) *
          (Real.exp s.quantum.vacuum.logRatio *
            Real.exp s.levelLocked.hierarchyExponent) =
        (s.quantum.mcsScale.levelMagnitude *
          s.quantum.vacuum.renormalizationMass *
          Real.exp s.quantum.vacuum.logRatio) *
          (s.levelLocked.uvLength *
            Real.exp s.levelLocked.hierarchyExponent) := by ring
      _ =
        (s.quantum.mcsScale.levelMagnitude *
          s.quantum.vacuum.renormalizationMass *
          Real.exp s.quantum.vacuum.logRatio) *
          (2 * s.quantum.vacuum.alphaSquaredLength) := by
            rw [← hRG]
      _ = 2 *
        (s.quantum.mcsScale.levelMagnitude *
          (s.quantum.vacuum.renormalizationMass *
            Real.exp s.quantum.vacuum.logRatio) *
          s.quantum.vacuum.alphaSquaredLength) := by ring
      _ = 2 * Real.pi := by rw [hMCS]
  rw [s.reciprocalUVAnchor] at hProduct
  norm_num at hProduct
  calc
    (s.levelLocked.chernSimonsLevel : ℝ) *
        Real.exp
          (s.quantum.vacuum.logRatio +
            s.levelLocked.hierarchyExponent) =
      s.quantum.mcsScale.levelMagnitude *
        (Real.exp s.quantum.vacuum.logRatio *
          Real.exp s.levelLocked.hierarchyExponent) := by
            rw [s.sameLevel, Real.exp_add]
    _ = 2 * Real.pi := hProduct

/-- Primitive level gives `exp(x_*+X)=2*pi`. -/
theorem primitive_level_corrected_matching
    (s : CorrectedDiscreteMCSMatching)
    (hLevel : s.levelLocked.chernSimonsLevel = 1) :
    Real.exp
        (s.quantum.vacuum.logRatio +
          s.levelLocked.hierarchyExponent) =
      2 * Real.pi := by
  have h := corrected_exponent_matching s
  rw [hLevel] at h
  norm_num at h ⊢
  exact h

/--
The older exact-cancellation ansatz `x_*+X=0` would force the level magnitude
to equal `2*pi`; therefore it cannot simultaneously be treated as the standard
unit integer level without changing the charge normalization.
-/
theorem exact_exponent_cancellation_forces_level_two_pi
    (s : CorrectedDiscreteMCSMatching)
    (hCancellation :
      s.quantum.vacuum.logRatio +
        s.levelLocked.hierarchyExponent = 0) :
    (s.levelLocked.chernSimonsLevel : ℝ) =
      2 * Real.pi := by
  have h := corrected_exponent_matching s
  rw [hCancellation, Real.exp_zero, mul_one] at h
  exact h

/--
This corrected relation removes the arbitrary unit-amplitude convention.  A
fully discrete prediction still requires computation of the level-lock constant,
the sextic beta function and the anomaly-allowed realized level.
-/
structure CorrectedDiscreteClosureStatus where
  mcsPoleMassNormalizationDerived : Prop
  chargeAmplitudeLevelLockDerived : Prop
  reciprocalUVAnchorDerived : Prop
  integerLevelSharedAcrossDescriptions : Prop
  correctedExponentMatchingDerived : Prop
  betaFunctionComputed : Prop
  levelLockConstantComputed : Prop
  anomalyAllowedLevelSelected : Prop
  stableVacuumBeyondLeadingLog : Prop
  absoluteAlphaPredicted : Prop


def correctedDiscreteClosure
    (s : CorrectedDiscreteClosureStatus) : Prop :=
  s.mcsPoleMassNormalizationDerived /\
  s.chargeAmplitudeLevelLockDerived /\
  s.reciprocalUVAnchorDerived /\
  s.integerLevelSharedAcrossDescriptions /\
  s.correctedExponentMatchingDerived /\
  s.betaFunctionComputed /\
  s.levelLockConstantComputed /\
  s.anomalyAllowedLevelSelected /\
  s.stableVacuumBeyondLeadingLog /\
  s.absoluteAlphaPredicted

end P0EFTJanusCorrectedDiscreteMCSMatching
end JanusFormal

import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusRGInvariantMCSAlpha

namespace JanusFormal
namespace P0EFTJanusMCSAmplitudeLock

set_option autoImplicit false

open P0EFTJanusRGImprovedSexticVacuum
open P0EFTJanusMaxwellChernSimonsChargeNormalization
open P0EFTJanusRGInvariantMCSAlpha

/--
Consistency of the generic condensate normalization with the
Maxwell--Chern--Simons pole-mass normalization removes the formerly arbitrary
charge amplitude:

`2*pi*a_q = K`.
-/
theorem charge_amplitude_locked_by_level
    (s : RGInvariantMCSAlpha) :
    2 * Real.pi * s.vacuum.chargeAmplitude =
      s.mcsScale.levelMagnitude := by
  have hVacuum := stable_vacuum_fixes_alpha_relation s.vacuum
  have hMCS := level_condensate_alpha_law s.mcsScale
  rw [s.sameCondensate, s.sameAlpha] at hMCS
  have hCondensateAlphaPositive :
      0 < s.vacuum.condensateMass *
        s.vacuum.alphaSquaredLength :=
    mul_pos s.vacuum.condensateMassPositive
      s.vacuum.alphaSquaredLengthPositive
  have hEquality :
      (2 * Real.pi * s.vacuum.chargeAmplitude) *
          (s.vacuum.condensateMass *
            s.vacuum.alphaSquaredLength) =
        s.mcsScale.levelMagnitude *
          (s.vacuum.condensateMass *
            s.vacuum.alphaSquaredLength) := by
    calc
      (2 * Real.pi * s.vacuum.chargeAmplitude) *
          (s.vacuum.condensateMass *
            s.vacuum.alphaSquaredLength) =
        Real.pi *
          (2 * s.vacuum.chargeAmplitude *
            s.vacuum.condensateMass *
            s.vacuum.alphaSquaredLength) := by ring
      _ = Real.pi := by rw [hVacuum]; ring
      _ = s.mcsScale.levelMagnitude *
          s.vacuum.condensateMass *
          s.vacuum.alphaSquaredLength := hMCS.symm
      _ = s.mcsScale.levelMagnitude *
          (s.vacuum.condensateMass *
            s.vacuum.alphaSquaredLength) := by ring
  have hFactor :
      (2 * Real.pi * s.vacuum.chargeAmplitude -
        s.mcsScale.levelMagnitude) *
        (s.vacuum.condensateMass *
          s.vacuum.alphaSquaredLength) = 0 := by
    nlinarith [hEquality]
  have hNonzero :
      s.vacuum.condensateMass *
        s.vacuum.alphaSquaredLength ≠ 0 :=
    ne_of_gt hCondensateAlphaPositive
  have hDifference :
      2 * Real.pi * s.vacuum.chargeAmplitude -
        s.mcsScale.levelMagnitude = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right hNonzero
  linarith

/-- Unit level fixes the dimensionless amplitude to `1/(2*pi)` in cleared form. -/
theorem unit_level_amplitude_law
    (s : RGInvariantMCSAlpha)
    (hUnit : s.mcsScale.levelMagnitude = 1) :
    2 * Real.pi * s.vacuum.chargeAmplitude = 1 := by
  rw [charge_amplitude_locked_by_level s, hUnit]

/--
The remaining normalization claim is now the physical identification of the LL
flux unit with the squared Maxwell--Chern--Simons pole mass; no continuous
amplitude remains once that identification and the integer level are derived.
-/
structure AmplitudeLockStatus where
  compactLevelQuantized : Prop
  mcsPoleMassDerived : Prop
  llChargeEqualsPoleMassSquared : Prop
  genericCondensateNormalizationDerived : Prop
  chargeAmplitudeLevelLockProved : Prop
  anomalyAllowedLevelSelected : Prop


def amplitudeLockClosed (s : AmplitudeLockStatus) : Prop :=
  s.compactLevelQuantized /\
  s.mcsPoleMassDerived /\
  s.llChargeEqualsPoleMassSquared /\
  s.genericCondensateNormalizationDerived /\
  s.chargeAmplitudeLevelLockProved /\
  s.anomalyAllowedLevelSelected

end P0EFTJanusMCSAmplitudeLock
end JanusFormal

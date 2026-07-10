import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusRGImprovedSexticVacuum

namespace JanusFormal
namespace P0EFTJanusCondensateBridgeSpectrum

set_option autoImplicit false

open P0EFTJanusRGImprovedSexticVacuum

/--
End-to-end conditional spectrum: the one-log quantum condensate fixes the Janus
length, which fixes the bridge mass, signed global mass and LL tension.
-/
structure CondensateBridgeSpectrum where
  vacuum : OneLogAlphaVacuum
  lightSpeedSquared : ℝ
  gravitationalConstant : ℝ
  piConstant : ℝ
  bridgeMass : ℝ
  globalMassConstant : ℝ
  llTensionMagnitude : ℝ
  gravitationalConstantNonzero : gravitationalConstant ≠ 0
  piConstantNonzero : piConstant ≠ 0
  schwarzschildBridgeLaw :
    lightSpeedSquared * vacuum.alphaSquaredLength =
      2 * gravitationalConstant * bridgeMass
  globalMassBridgeLaw :
    4 * piConstant * globalMassConstant + 3 * bridgeMass = 0
  llTensionLaw :
    8 * piConstant * llTensionMagnitude *
      vacuum.alphaSquaredLength = 1

/-- Condensate and charge amplitude determine the bridge mass. -/
theorem condensate_bridge_mass_law
    (s : CondensateBridgeSpectrum) :
    4 * s.gravitationalConstant * s.vacuum.chargeAmplitude *
        s.vacuum.condensateMass * s.bridgeMass =
      s.lightSpeedSquared := by
  have hAlpha := stable_vacuum_fixes_alpha_relation s.vacuum
  have hBridge := s.schwarzschildBridgeLaw
  calc
    4 * s.gravitationalConstant * s.vacuum.chargeAmplitude *
        s.vacuum.condensateMass * s.bridgeMass =
      (2 * s.vacuum.chargeAmplitude * s.vacuum.condensateMass *
        s.vacuum.alphaSquaredLength) *
        (2 * s.gravitationalConstant * s.bridgeMass) := by
          rw [hAlpha]
          ring
    _ = 1 *
        (s.lightSpeedSquared * s.vacuum.alphaSquaredLength) := by
          rw [hBridge]
    _ = s.lightSpeedSquared := by
          rw [hAlpha]
          ring

/-- Condensate and charge amplitude determine the LL tension. -/
theorem condensate_tension_law
    (s : CondensateBridgeSpectrum) :
    4 * s.piConstant * s.llTensionMagnitude =
      s.vacuum.chargeAmplitude * s.vacuum.condensateMass := by
  have hAlpha := stable_vacuum_fixes_alpha_relation s.vacuum
  have hTension := s.llTensionLaw
  have hFactor :
      2 * s.vacuum.alphaSquaredLength *
        (4 * s.piConstant * s.llTensionMagnitude -
          s.vacuum.chargeAmplitude * s.vacuum.condensateMass) = 0 := by
    calc
      2 * s.vacuum.alphaSquaredLength *
          (4 * s.piConstant * s.llTensionMagnitude -
            s.vacuum.chargeAmplitude * s.vacuum.condensateMass) =
        8 * s.piConstant * s.llTensionMagnitude *
            s.vacuum.alphaSquaredLength -
          2 * s.vacuum.chargeAmplitude * s.vacuum.condensateMass *
            s.vacuum.alphaSquaredLength := by ring
      _ = 1 - 1 := by rw [hTension, hAlpha]
      _ = 0 := by norm_num
  have hAlphaNonzero : 2 * s.vacuum.alphaSquaredLength ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt s.vacuum.alphaSquaredLengthPositive)
  have hDifference :
      4 * s.piConstant * s.llTensionMagnitude -
        s.vacuum.chargeAmplitude * s.vacuum.condensateMass = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hAlphaNonzero
  linarith

/-- Condensate and charge amplitude determine the signed global mass constant. -/
theorem condensate_global_mass_law
    (s : CondensateBridgeSpectrum) :
    16 * s.piConstant * s.gravitationalConstant *
        s.vacuum.chargeAmplitude * s.vacuum.condensateMass *
        s.globalMassConstant +
      3 * s.lightSpeedSquared = 0 := by
  have hBridge := condensate_bridge_mass_law s
  have hGlobal := s.globalMassBridgeLaw
  calc
    16 * s.piConstant * s.gravitationalConstant *
          s.vacuum.chargeAmplitude * s.vacuum.condensateMass *
          s.globalMassConstant +
        3 * s.lightSpeedSquared =
      4 * s.gravitationalConstant * s.vacuum.chargeAmplitude *
        s.vacuum.condensateMass *
        (4 * s.piConstant * s.globalMassConstant +
          3 * s.bridgeMass) := by
            rw [hBridge]
            ring
    _ = 0 := by rw [hGlobal]; ring

/-- Substitute the one-log minimum explicitly into the bridge-mass equation. -/
theorem microscopic_bridge_mass_equation
    (s : CondensateBridgeSpectrum) :
    4 * s.gravitationalConstant * s.vacuum.chargeAmplitude *
        s.vacuum.renormalizationMass * Real.exp s.vacuum.logRatio *
        s.bridgeMass = s.lightSpeedSquared := by
  have h := condensate_bridge_mass_law s
  rw [s.vacuum.condensateLaw] at h
  simpa [mul_assoc] using h

/-- Substitute the one-log minimum explicitly into the tension equation. -/
theorem microscopic_tension_equation
    (s : CondensateBridgeSpectrum) :
    4 * s.piConstant * s.llTensionMagnitude =
      s.vacuum.chargeAmplitude * s.vacuum.renormalizationMass *
        Real.exp s.vacuum.logRatio := by
  have h := condensate_tension_law s
  rw [s.vacuum.condensateLaw] at h
  simpa [mul_assoc] using h

/-- All terminal condensate-controlled relations hold simultaneously. -/
theorem complete_condensate_bridge_spectrum
    (s : CondensateBridgeSpectrum) :
    (2 * s.vacuum.chargeAmplitude * s.vacuum.condensateMass *
      s.vacuum.alphaSquaredLength = 1) /\
    (4 * s.gravitationalConstant * s.vacuum.chargeAmplitude *
      s.vacuum.condensateMass * s.bridgeMass = s.lightSpeedSquared) /\
    (4 * s.piConstant * s.llTensionMagnitude =
      s.vacuum.chargeAmplitude * s.vacuum.condensateMass) /\
    (16 * s.piConstant * s.gravitationalConstant *
      s.vacuum.chargeAmplitude * s.vacuum.condensateMass *
      s.globalMassConstant + 3 * s.lightSpeedSquared = 0) := by
  exact ⟨stable_vacuum_fixes_alpha_relation s.vacuum,
    condensate_bridge_mass_law s,
    condensate_tension_law s,
    condensate_global_mass_law s⟩

end P0EFTJanusCondensateBridgeSpectrum
end JanusFormal

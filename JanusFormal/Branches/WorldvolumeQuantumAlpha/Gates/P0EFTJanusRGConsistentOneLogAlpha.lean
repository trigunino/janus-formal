import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusRGImprovedSexticVacuum

namespace JanusFormal
namespace P0EFTJanusRGConsistentOneLogAlpha

set_option autoImplicit false

open P0EFTJanusRGImprovedSexticVacuum

/--
Callan--Symanzik consistency for the one-log composite potential

`V(σ) = σ^3 * (lambda6 + b * log(σ/mu))`.

At this truncation and with anomalous-dimension effects kept outside the scalar
coefficient, RG invariance identifies the logarithmic coefficient with the beta
function of `lambda6` at the subtraction scale.
-/
structure RGConsistentOneLogAlpha extends OneLogAlphaVacuum where
  betaSextic : ℝ
  callanSymanzikCoefficientLaw : betaSextic = logCoefficient

/-- The stationary logarithm is determined directly by the beta function. -/
theorem beta_stationarity_equation
    (s : RGConsistentOneLogAlpha) :
    3 * s.betaSextic * s.logRatio =
      -(3 * s.sexticCoupling + s.betaSextic) := by
  rw [s.callanSymanzikCoefficientLaw]
  exact stationary_log_equation s.toOneLogAlphaVacuum.toOneLogCompositeVacuum

/-- The exact microscopic alpha equation survives the RG identification. -/
theorem beta_improved_alpha_equation
    (s : RGConsistentOneLogAlpha) :
    2 * s.chargeAmplitude * s.renormalizationMass *
        Real.exp s.logRatio * s.alphaSquaredLength = 1 := by
  exact microscopic_alpha_equation s.toOneLogAlphaVacuum

/-- Positive logarithmic coefficient implies a positive sextic beta function. -/
theorem beta_sextic_positive
    (s : RGConsistentOneLogAlpha) :
    0 < s.betaSextic := by
  rw [s.callanSymanzikCoefficientLaw]
  exact s.logCoefficientPositive

/-- Equal RG data and charge normalization select the same Janus length. -/
theorem same_rg_data_fix_same_alpha
    (s₁ s₂ : RGConsistentOneLogAlpha)
    (hMu : s₁.renormalizationMass = s₂.renormalizationMass)
    (hLambda : s₁.sexticCoupling = s₂.sexticCoupling)
    (hBeta : s₁.betaSextic = s₂.betaSextic)
    (hAmplitude : s₁.chargeAmplitude = s₂.chargeAmplitude) :
    s₁.alphaSquaredLength = s₂.alphaSquaredLength := by
  apply same_microscopic_vacuum_data_fix_alpha
    s₁.toOneLogAlphaVacuum s₂.toOneLogAlphaVacuum hMu hLambda
  · calc
      s₁.logCoefficient = s₁.betaSextic :=
        s₁.callanSymanzikCoefficientLaw.symm
      _ = s₂.betaSextic := hBeta
      _ = s₂.logCoefficient :=
        s₂.callanSymanzikCoefficientLaw
  · exact hAmplitude

/--
At fixed positive beta function, increasing the sextic coupling decreases the
condensate and therefore increases the selected Janus length.
-/
theorem larger_sextic_coupling_gives_larger_alpha
    (s₁ s₂ : RGConsistentOneLogAlpha)
    (hMu : s₁.renormalizationMass = s₂.renormalizationMass)
    (hBeta : s₁.betaSextic = s₂.betaSextic)
    (hAmplitude : s₁.chargeAmplitude = s₂.chargeAmplitude)
    (hLambda : s₁.sexticCoupling < s₂.sexticCoupling) :
    s₁.alphaSquaredLength < s₂.alphaSquaredLength := by
  have hBetaPositive : 0 < s₁.betaSextic := beta_sextic_positive s₁
  have hStationary₁ := beta_stationarity_equation s₁
  have hStationary₂ := beta_stationarity_equation s₂
  rw [← hBeta] at hStationary₂
  have hLog : s₂.logRatio < s₁.logRatio := by
    nlinarith
  have hExp : Real.exp s₂.logRatio < Real.exp s₁.logRatio :=
    Real.exp_lt_exp.mpr hLog
  have hMuPositive : 0 < s₁.renormalizationMass :=
    s₁.renormalizationMassPositive
  have hCondensate : s₂.condensateMass < s₁.condensateMass := by
    calc
      s₂.condensateMass =
          s₂.renormalizationMass * Real.exp s₂.logRatio :=
        s₂.condensateLaw
      _ = s₁.renormalizationMass * Real.exp s₂.logRatio := by rw [← hMu]
      _ < s₁.renormalizationMass * Real.exp s₁.logRatio :=
        mul_lt_mul_of_pos_left hExp hMuPositive
      _ = s₁.condensateMass := s₁.condensateLaw.symm
  have hLaw₁ := stable_vacuum_fixes_alpha_relation s₁.toOneLogAlphaVacuum
  have hLaw₂ := stable_vacuum_fixes_alpha_relation s₂.toOneLogAlphaVacuum
  rw [← hAmplitude] at hLaw₂
  have hAmplitudePositive : 0 < s₁.chargeAmplitude :=
    s₁.chargeAmplitudePositive
  by_contra hNot
  have hAlphaOrder : s₂.alphaSquaredLength ≤ s₁.alphaSquaredLength :=
    le_of_not_gt hNot
  have hProductStrict :
      2 * s₁.chargeAmplitude * s₂.condensateMass *
          s₂.alphaSquaredLength <
        2 * s₁.chargeAmplitude * s₁.condensateMass *
          s₁.alphaSquaredLength := by
    have hLeftPositive : 0 < 2 * s₁.chargeAmplitude := by positivity
    have hMixed :
        s₂.condensateMass * s₂.alphaSquaredLength <
          s₁.condensateMass * s₁.alphaSquaredLength := by
      have hAlphaPositive : 0 < s₂.alphaSquaredLength :=
        s₂.alphaSquaredLengthPositive
      calc
        s₂.condensateMass * s₂.alphaSquaredLength <
            s₁.condensateMass * s₂.alphaSquaredLength :=
          mul_lt_mul_of_pos_right hCondensate hAlphaPositive
        _ ≤ s₁.condensateMass * s₁.alphaSquaredLength :=
          mul_le_mul_of_nonneg_left hAlphaOrder
            (le_of_lt s₁.condensateMassPositive)
    exact mul_lt_mul_of_pos_left hMixed hLeftPositive
  rw [hLaw₁, hLaw₂] at hProductStrict
  linarith

end P0EFTJanusRGConsistentOneLogAlpha
end JanusFormal

import Mathlib

namespace JanusFormal
namespace P0EFTJanusLeeClassQuantizedHierarchy

set_option autoImplicit false

/--
Candidate integral Lee-class law for the logarithmic Hopf period:

`T = 2*pi*n`, with positive integer `n`.
-/
structure QuantizedLeeHierarchy where
  uvLength : ℝ
  alphaSquaredLength : ℝ
  piConstant : ℝ
  leeLevel : ℕ
  tunnelPeriod : ℝ
  uvLengthPositive : 0 < uvLength
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  piConstantPositive : 0 < piConstant
  leeLevelPositive : 0 < leeLevel
  leePeriodQuantization :
    tunnelPeriod = 2 * piConstant * (leeLevel : ℝ)
  geometricHierarchyLaw :
    2 * alphaSquaredLength = uvLength * Real.exp tunnelPeriod

/-- The quantized Lee class gives a discrete absolute hierarchy formula. -/
theorem quantized_lee_alpha_law
    (s : QuantizedLeeHierarchy) :
    2 * s.alphaSquaredLength =
      s.uvLength *
        Real.exp (2 * s.piConstant * (s.leeLevel : ℝ)) := by
  rw [s.geometricHierarchyLaw, s.leePeriodQuantization]

/-- Same UV anchor, pi convention and Lee level give the same Janus length. -/
theorem same_lee_data_fix_alpha
    (s₁ s₂ : QuantizedLeeHierarchy)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hPi : s₁.piConstant = s₂.piConstant)
    (hLevel : s₁.leeLevel = s₂.leeLevel) :
    s₁.alphaSquaredLength = s₂.alphaSquaredLength := by
  have h₁ := quantized_lee_alpha_law s₁
  have h₂ := quantized_lee_alpha_law s₂
  rw [hUV, hPi, hLevel] at h₁
  linarith

/-- Adjacent Lee levels differ by the universal multiplicative factor `exp(2*pi)`. -/
theorem adjacent_lee_levels_have_exponential_spacing
    (s₁ s₂ : QuantizedLeeHierarchy)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hPi : s₁.piConstant = s₂.piConstant)
    (hAdjacent : s₂.leeLevel = s₁.leeLevel + 1) :
    s₂.alphaSquaredLength =
      Real.exp (2 * s₁.piConstant) * s₁.alphaSquaredLength := by
  have h₁ := quantized_lee_alpha_law s₁
  have h₂ := quantized_lee_alpha_law s₂
  rw [hUV, hPi, hAdjacent] at h₂
  norm_num [Nat.cast_add, Nat.cast_one] at h₂
  have hExponent :
      2 * s₁.piConstant * ((s₁.leeLevel : ℝ) + 1) =
        2 * s₁.piConstant * (s₁.leeLevel : ℝ) +
          2 * s₁.piConstant := by ring
  rw [hExponent, Real.exp_add] at h₂
  have hTwoNonzero : (2 : ℝ) ≠ 0 := by norm_num
  have hScaled :
      2 * s₂.alphaSquaredLength =
        Real.exp (2 * s₁.piConstant) *
          (2 * s₁.alphaSquaredLength) := by
    calc
      2 * s₂.alphaSquaredLength =
          s₁.uvLength *
            (Real.exp (2 * s₁.piConstant * (s₁.leeLevel : ℝ)) *
              Real.exp (2 * s₁.piConstant)) := h₂
      _ = Real.exp (2 * s₁.piConstant) *
          (s₁.uvLength *
            Real.exp (2 * s₁.piConstant * (s₁.leeLevel : ℝ))) := by ring
      _ = Real.exp (2 * s₁.piConstant) *
          (2 * s₁.alphaSquaredLength) := by rw [← h₁]
  nlinarith

/--
Integral Lee quantization is predictive only if the Weyl/Lee connection is
proved compact and its realized integer level is selected.  Its very coarse
spacing may require an additional vacuum amplitude or fractional normalization.
-/
structure LeeQuantizationClosureStatus where
  leeFormDerivedFromConformalMetric : Prop
  leeClassGeneratorComputed : Prop
  compactWeylGaugeGroupDerived : Prop
  integralPeriodLawDerived : Prop
  realizedLeeLevelSelected : Prop
  levelSpacingPhenomenologicallyViable : Prop
  uvAnchorDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaDerived : Prop


def leeQuantizationClosure
    (s : LeeQuantizationClosureStatus) : Prop :=
  s.leeFormDerivedFromConformalMetric /\
  s.leeClassGeneratorComputed /\
  s.compactWeylGaugeGroupDerived /\
  s.integralPeriodLawDerived /\
  s.realizedLeeLevelSelected /\
  s.levelSpacingPhenomenologicallyViable /\
  s.uvAnchorDerived /\
  s.noObservedScaleImported /\
  s.absoluteAlphaDerived

end P0EFTJanusLeeClassQuantizedHierarchy
end JanusFormal

import Mathlib
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusPrimitiveChargeAreaScaleLaw

namespace JanusFormal
namespace P0EFTJanusWorldvolumeRGTransmutation

set_option autoImplicit false

open P0EFTJanusPrimitiveChargeAreaScaleLaw

/--
Planck-anchored dimensional transmutation on the `2+1` dimensional LL
world-volume.

The convention is

`B * X = 8*pi^2`,
`ell_dyn = ell_UV * exp(X)`,
`q_LL * ell_dyn^2 = 1`,
`16*q_LL^2*A^4 = 1`.

Here `A` is the positive length denoted `alpha^2` in the 2018 exact solution.
The structure deliberately separates the RG exponent from the physical claim
that a particular quantum theory computes it.
-/
structure RGTransmutedLLScale where
  uvLength : ℝ
  betaCouplingProduct : ℝ
  hierarchyExponent : ℝ
  generatedLength : ℝ
  chargeUnit : ℝ
  alphaSquaredLength : ℝ
  uvLengthPositive : 0 < uvLength
  betaCouplingProductPositive : 0 < betaCouplingProduct
  generatedLengthPositive : 0 < generatedLength
  chargeUnitPositive : 0 < chargeUnit
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  rgExponentLaw :
    betaCouplingProduct * hierarchyExponent = 8 * Real.pi ^ 2
  transmutationLaw :
    generatedLength = uvLength * Real.exp hierarchyExponent
  chargeAreaNormalization :
    chargeUnit * generatedLength ^ 2 = 1
  primitiveRadiusLaw :
    16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- Repackage the RG output as the previously proved primitive area law. -/
def asFundamentalAreaNormalizedFlux
    (s : RGTransmutedLLScale) : FundamentalAreaNormalizedFlux :=
  { chargeUnit := s.chargeUnit
    fundamentalLength := s.generatedLength
    throatRadius := s.alphaSquaredLength
    chargeUnitPositive := s.chargeUnitPositive
    fundamentalLengthPositive := s.generatedLengthPositive
    throatRadiusPositive := s.alphaSquaredLengthPositive
    chargeAreaNormalization := s.chargeAreaNormalization
    primitiveRadiusLaw := s.primitiveRadiusLaw }

/-- Primitive flux fixes the Janus length to half the generated quantum length. -/
theorem twice_alpha_eq_generated_length
    (s : RGTransmutedLLScale) :
    2 * s.alphaSquaredLength = s.generatedLength := by
  exact primitive_radius_is_half_fundamental_length
    (asFundamentalAreaNormalizedFlux s)

/-- Complete hierarchy relation in a division-free form. -/
theorem planck_anchored_hierarchy_law
    (s : RGTransmutedLLScale) :
    2 * s.alphaSquaredLength =
      s.uvLength * Real.exp s.hierarchyExponent := by
  calc
    2 * s.alphaSquaredLength = s.generatedLength :=
      twice_alpha_eq_generated_length s
    _ = s.uvLength * Real.exp s.hierarchyExponent :=
      s.transmutationLaw

/-- A fixed positive beta/coupling product fixes the RG exponent. -/
theorem same_beta_product_fixes_exponent
    (s₁ s₂ : RGTransmutedLLScale)
    (hProduct :
      s₁.betaCouplingProduct = s₂.betaCouplingProduct) :
    s₁.hierarchyExponent = s₂.hierarchyExponent := by
  have h₁ := s₁.rgExponentLaw
  have h₂ := s₂.rgExponentLaw
  rw [← hProduct] at h₂
  have hFactor :
      s₁.betaCouplingProduct *
        (s₁.hierarchyExponent - s₂.hierarchyExponent) = 0 := by
    nlinarith [h₁, h₂]
  have hNonzero : s₁.betaCouplingProduct ≠ 0 :=
    ne_of_gt s₁.betaCouplingProductPositive
  have hDifference :
      s₁.hierarchyExponent - s₂.hierarchyExponent = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hNonzero
  linarith

/-- The UV length and RG product uniquely determine the conditional Janus length. -/
theorem same_uv_and_beta_product_fix_alpha
    (s₁ s₂ : RGTransmutedLLScale)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hProduct :
      s₁.betaCouplingProduct = s₂.betaCouplingProduct) :
    s₁.alphaSquaredLength = s₂.alphaSquaredLength := by
  have hExponent := same_beta_product_fixes_exponent s₁ s₂ hProduct
  have h₁ := planck_anchored_hierarchy_law s₁
  have h₂ := planck_anchored_hierarchy_law s₂
  rw [hUV, hExponent] at h₁
  linarith

/-- Larger hierarchy exponent produces a strictly larger Janus length. -/
theorem exponent_strictly_orders_alpha
    (s₁ s₂ : RGTransmutedLLScale)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hExponent : s₁.hierarchyExponent < s₂.hierarchyExponent) :
    s₁.alphaSquaredLength < s₂.alphaSquaredLength := by
  have hExp :
      Real.exp s₁.hierarchyExponent < Real.exp s₂.hierarchyExponent :=
    Real.exp_lt_exp.mpr hExponent
  have hScaled :
      s₁.uvLength * Real.exp s₁.hierarchyExponent <
        s₁.uvLength * Real.exp s₂.hierarchyExponent :=
    mul_lt_mul_of_pos_left hExp s₁.uvLengthPositive
  have h₁ := planck_anchored_hierarchy_law s₁
  have h₂ := planck_anchored_hierarchy_law s₂
  rw [← hUV] at h₂
  linarith

/--
The quantum theory is predictive only after the UV product, normalization and
vacuum are all selected independently of the target cosmological radius.
-/
structure WorldvolumeQuantumClosureStatus where
  compactGaugeBundleDerived : Prop
  parityAndGlobalAnomaliesCancelled : Prop
  renormalizedEffectiveActionDerived : Prop
  stableQuantumVacuumProved : Prop
  betaCoefficientComputed : Prop
  uvCouplingFixedByMicroscopicLaw : Prop
  uvAnchorFixedByBulkGravity : Prop
  chargeOperatorNormalizationDerived : Prop
  primitiveFluxSectorSelected : Prop
  lorentzianContinuationControlled : Prop
  noObservedScaleImported : Prop
  absoluteAlphaScaleDerived : Prop


def worldvolumeQuantumClosure
    (s : WorldvolumeQuantumClosureStatus) : Prop :=
  s.compactGaugeBundleDerived /\
  s.parityAndGlobalAnomaliesCancelled /\
  s.renormalizedEffectiveActionDerived /\
  s.stableQuantumVacuumProved /\
  s.betaCoefficientComputed /\
  s.uvCouplingFixedByMicroscopicLaw /\
  s.uvAnchorFixedByBulkGravity /\
  s.chargeOperatorNormalizationDerived /\
  s.primitiveFluxSectorSelected /\
  s.lorentzianContinuationControlled /\
  s.noObservedScaleImported /\
  s.absoluteAlphaScaleDerived

end P0EFTJanusWorldvolumeRGTransmutation
end JanusFormal

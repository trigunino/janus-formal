import Mathlib

namespace JanusFormal
namespace P0EFTJanusRGHeatKernelAbsoluteScale

set_option autoImplicit false

/--
Dimensional transmutation plus the nonlocal spectral vacuum.

The convention is

`B*X = 8*pi^2`,
`m_dyn * exp(X) = mu_UV`,
`m_dyn * T * A = x_*`.
-/
structure RGHeatKernelScale where
  uvMass : ℝ
  betaCouplingProduct : ℝ
  hierarchyExponent : ℝ
  generatedMass : ℝ
  circleModulus : ℝ
  stationaryProduct : ℝ
  alphaSquaredLength : ℝ
  piConstant : ℝ
  uvMassPositive : 0 < uvMass
  betaCouplingProductPositive : 0 < betaCouplingProduct
  generatedMassPositive : 0 < generatedMass
  circleModulusPositive : 0 < circleModulus
  stationaryProductPositive : 0 < stationaryProduct
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  piConstantPositive : 0 < piConstant
  rgExponentLaw :
    betaCouplingProduct * hierarchyExponent = 8 * piConstant ^ 2
  massTransmutationLaw :
    generatedMass * Real.exp hierarchyExponent = uvMass
  spectralVacuumLaw :
    generatedMass * circleModulus * alphaSquaredLength =
      stationaryProduct

/-- Complete exponential hierarchy law. -/
theorem rg_spectral_hierarchy_law
    (s : RGHeatKernelScale) :
    s.uvMass * s.circleModulus * s.alphaSquaredLength =
      s.stationaryProduct * Real.exp s.hierarchyExponent := by
  calc
    s.uvMass * s.circleModulus * s.alphaSquaredLength =
        (s.generatedMass * Real.exp s.hierarchyExponent) *
          s.circleModulus * s.alphaSquaredLength := by
      rw [s.massTransmutationLaw]
    _ = Real.exp s.hierarchyExponent *
        (s.generatedMass * s.circleModulus *
          s.alphaSquaredLength) := by ring
    _ = s.stationaryProduct * Real.exp s.hierarchyExponent := by
      rw [s.spectralVacuumLaw]
      ring

/-- Division form of the absolute length. -/
theorem rg_spectral_alpha_division_law
    (s : RGHeatKernelScale) :
    s.alphaSquaredLength =
      s.stationaryProduct * Real.exp s.hierarchyExponent /
        (s.uvMass * s.circleModulus) := by
  have hHierarchy := rg_spectral_hierarchy_law s
  have hNonzero : s.uvMass * s.circleModulus ≠ 0 :=
    mul_ne_zero (ne_of_gt s.uvMassPositive)
      (ne_of_gt s.circleModulusPositive)
  apply (eq_div_iff hNonzero).2
  nlinarith [hHierarchy]

/-- Fixed positive RG product fixes the hierarchy exponent. -/
theorem same_beta_product_fixes_hierarchy_exponent
    (first second : RGHeatKernelScale)
    (hProduct :
      first.betaCouplingProduct = second.betaCouplingProduct)
    (hPi : first.piConstant = second.piConstant) :
    first.hierarchyExponent = second.hierarchyExponent := by
  have hFirst := first.rgExponentLaw
  have hSecond := second.rgExponentLaw
  rw [← hProduct, ← hPi] at hSecond
  have hFactor :
      first.betaCouplingProduct *
        (first.hierarchyExponent - second.hierarchyExponent) = 0 := by
    nlinarith [hFirst, hSecond]
  have hProductNonzero : first.betaCouplingProduct ≠ 0 :=
    ne_of_gt first.betaCouplingProductPositive
  have hDifference :
      first.hierarchyExponent - second.hierarchyExponent = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hProductNonzero
  linarith

/-- Same microscopic and spectral data give the same absolute alpha. -/
theorem same_rg_and_spectral_data_fix_same_alpha
    (first second : RGHeatKernelScale)
    (hUV : first.uvMass = second.uvMass)
    (hProduct :
      first.betaCouplingProduct = second.betaCouplingProduct)
    (hPi : first.piConstant = second.piConstant)
    (hModulus : first.circleModulus = second.circleModulus)
    (hStationary :
      first.stationaryProduct = second.stationaryProduct) :
    first.alphaSquaredLength = second.alphaSquaredLength := by
  have hExponent := same_beta_product_fixes_hierarchy_exponent
    first second hProduct hPi
  have hFirst := rg_spectral_hierarchy_law first
  have hSecond := rg_spectral_hierarchy_law second
  rw [hUV, hModulus, hStationary, hExponent] at hFirst
  have hPositive :
      0 < second.uvMass * second.circleModulus :=
    mul_pos second.uvMassPositive second.circleModulusPositive
  nlinarith [hFirst, hSecond]

/-- Larger hierarchy exponent gives larger alpha at fixed UV and spectral data. -/
theorem hierarchy_exponent_strictly_orders_alpha
    (first second : RGHeatKernelScale)
    (hUV : first.uvMass = second.uvMass)
    (hModulus : first.circleModulus = second.circleModulus)
    (hStationary :
      first.stationaryProduct = second.stationaryProduct)
    (hExponent : first.hierarchyExponent < second.hierarchyExponent) :
    first.alphaSquaredLength < second.alphaSquaredLength := by
  have hExp :
      Real.exp first.hierarchyExponent <
        Real.exp second.hierarchyExponent :=
    Real.exp_lt_exp.mpr hExponent
  have hFirst := rg_spectral_hierarchy_law first
  have hSecond := rg_spectral_hierarchy_law second
  rw [hUV, hModulus, hStationary] at hFirst
  have hCoefficientPositive :
      0 < second.uvMass * second.circleModulus :=
    mul_pos second.uvMassPositive second.circleModulusPositive
  nlinarith [hFirst, hSecond,
    mul_lt_mul_of_pos_left hExp second.stationaryProductPositive]

/--
This is the terminal formula, not yet a prediction: `B`, the UV mass, the
stationary product and the modulus must all be derived independently of the
target cosmological length.
-/
structure RGHeatKernelPhysicalClosureStatus where
  interactingBetaFunctionComputed : Prop
  uvCouplingFixedMicroscopically : Prop
  uvMassAnchoredByBulkGravity : Prop
  generatedMassDerived : Prop
  schemeIndependentEffectiveActionDerived : Prop
  stationaryProductDerived : Prop
  circleModulusDerived : Prop
  chargeAndBimetricLocksDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaDerived : Prop


def rgHeatKernelPhysicalClosure
    (s : RGHeatKernelPhysicalClosureStatus) : Prop :=
  s.interactingBetaFunctionComputed /\
  s.uvCouplingFixedMicroscopically /\
  s.uvMassAnchoredByBulkGravity /\
  s.generatedMassDerived /\
  s.schemeIndependentEffectiveActionDerived /\
  s.stationaryProductDerived /\
  s.circleModulusDerived /\
  s.chargeAndBimetricLocksDerived /\
  s.noObservedScaleImported /\
  s.absoluteAlphaDerived

end P0EFTJanusRGHeatKernelAbsoluteScale
end JanusFormal

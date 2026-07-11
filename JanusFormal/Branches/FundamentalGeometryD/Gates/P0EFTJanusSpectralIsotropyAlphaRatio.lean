import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpectralIsotropyAlphaRatio

set_option autoImplicit false

/--
Lowest-mode data on a product throat `S2_L x S1_(L*T)`.

The normalized first nonconstant scalar eigenvalue on `S2_L` is `2/L^2`; the
first circle eigenvalue is `(2*pi/(L*T))^2`.  All equations are stored in
cleared-denominator form.
-/
structure ThroatSpectralLock where
  geometricLength : ℝ
  circleModulus : ℝ
  piConstant : ℝ
  sphereFirstEigenvalue : ℝ
  circleFirstEigenvalue : ℝ
  chargeCoefficient : ℝ
  llChargeUnit : ℝ
  alphaSquaredLength : ℝ
  geometricLengthPositive : 0 < geometricLength
  circleModulusPositive : 0 < circleModulus
  piConstantPositive : 0 < piConstant
  sphereEigenvaluePositive : 0 < sphereFirstEigenvalue
  circleEigenvaluePositive : 0 < circleFirstEigenvalue
  chargeCoefficientPositive : 0 < chargeCoefficient
  llChargeUnitPositive : 0 < llChargeUnit
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  sphereModeLaw :
    sphereFirstEigenvalue * geometricLength ^ 2 = 2
  circleModeLaw :
    circleFirstEigenvalue * geometricLength ^ 2 * circleModulus ^ 2 =
      4 * piConstant ^ 2
  spectralIsotropy :
    sphereFirstEigenvalue = circleFirstEigenvalue
  chargeLockedToSphereGap :
    llChargeUnit * geometricLength ^ 2 = 2 * chargeCoefficient
  primitiveLLFluxLaw :
    16 * llChargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- Equal first sphere and circle modes fix the dimensionless circle modulus. -/
theorem spectral_isotropy_fixes_circle_modulus_squared
    (s : ThroatSpectralLock) :
    s.circleModulus ^ 2 = 2 * s.piConstant ^ 2 := by
  have hCircle := s.circleModeLaw
  rw [← s.spectralIsotropy] at hCircle
  have hSubstitution :
      (s.sphereFirstEigenvalue * s.geometricLength ^ 2) *
          s.circleModulus ^ 2 =
        4 * s.piConstant ^ 2 := by
    simpa [mul_assoc] using hCircle
  rw [s.sphereModeLaw] at hSubstitution
  nlinarith

/-- Squaring the spectral charge lock gives the required scale relation. -/
theorem charge_gap_square_law
    (s : ThroatSpectralLock) :
    s.llChargeUnit ^ 2 * s.geometricLength ^ 4 =
      4 * s.chargeCoefficient ^ 2 := by
  calc
    s.llChargeUnit ^ 2 * s.geometricLength ^ 4 =
        (s.llChargeUnit * s.geometricLength ^ 2) ^ 2 := by ring
    _ = (2 * s.chargeCoefficient) ^ 2 := by
      rw [s.chargeLockedToSphereGap]
    _ = 4 * s.chargeCoefficient ^ 2 := by ring

/--
The geometry/QFT lock fixes the dimensionless alpha ratio in cleared form:

`64*c_q^2*A^4 = L^4`.
-/
theorem spectral_lock_fixes_alpha_ratio_fourth_power
    (s : ThroatSpectralLock) :
    64 * s.chargeCoefficient ^ 2 * s.alphaSquaredLength ^ 4 =
      s.geometricLength ^ 4 := by
  have hChargeSquare := charge_gap_square_law s
  calc
    64 * s.chargeCoefficient ^ 2 * s.alphaSquaredLength ^ 4 =
        16 * (4 * s.chargeCoefficient ^ 2) *
          s.alphaSquaredLength ^ 4 := by ring
    _ = 16 *
        (s.llChargeUnit ^ 2 * s.geometricLength ^ 4) *
          s.alphaSquaredLength ^ 4 := by rw [← hChargeSquare]
    _ = (16 * s.llChargeUnit ^ 2 *
          s.alphaSquaredLength ^ 4) * s.geometricLength ^ 4 := by ring
    _ = s.geometricLength ^ 4 := by
      rw [s.primitiveLLFluxLaw]
      ring

/-- Unit charge normalization gives the positive ratio equation `8*A^2=L^2`. -/
theorem unit_charge_lock_fixes_alpha_ratio_squared
    (s : ThroatSpectralLock)
    (hUnit : s.chargeCoefficient = 1) :
    8 * s.alphaSquaredLength ^ 2 = s.geometricLength ^ 2 := by
  have hFourth := spectral_lock_fixes_alpha_ratio_fourth_power s
  rw [hUnit] at hFourth
  norm_num at hFourth
  have hSquares :
      (8 * s.alphaSquaredLength ^ 2) ^ 2 =
        (s.geometricLength ^ 2) ^ 2 := by
    calc
      (8 * s.alphaSquaredLength ^ 2) ^ 2 =
          64 * s.alphaSquaredLength ^ 4 := by ring
      _ = s.geometricLength ^ 4 := hFourth
      _ = (s.geometricLength ^ 2) ^ 2 := by ring
  have hFactor :
      (8 * s.alphaSquaredLength ^ 2 - s.geometricLength ^ 2) *
        (8 * s.alphaSquaredLength ^ 2 + s.geometricLength ^ 2) = 0 := by
    nlinarith [hSquares]
  rcases mul_eq_zero.mp hFactor with hDifference | hSum
  · linarith
  · have hPositive :
        0 < 8 * s.alphaSquaredLength ^ 2 +
          s.geometricLength ^ 2 := by
      positivity
    exact False.elim ((ne_of_gt hPositive) hSum)

/--
This is a conditional geometric prediction for `A/L`.  It becomes physical only
if the first spectral mode really sets the renormalized LL charge and the
coefficient is computed rather than normalized by hand.
-/
structure SpectralGeometryClosureStatus where
  productThroatMetricDerived : Prop
  spectralIsotropyDerived : Prop
  firstEigenmodeCondensateDerived : Prop
  chargeCoefficientComputed : Prop
  primitiveFluxSectorDerived : Prop
  alphaRatioDerived : Prop
  absoluteLengthDerived : Prop


def spectralGeometryClosure
    (s : SpectralGeometryClosureStatus) : Prop :=
  s.productThroatMetricDerived /\
  s.spectralIsotropyDerived /\
  s.firstEigenmodeCondensateDerived /\
  s.chargeCoefficientComputed /\
  s.primitiveFluxSectorDerived /\
  s.alphaRatioDerived /\
  s.absoluteLengthDerived

end P0EFTJanusSpectralIsotropyAlphaRatio
end JanusFormal

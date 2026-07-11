import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusSpectralIsotropyAlphaRatio

namespace JanusFormal
namespace P0EFTJanusSpectralBimetricConsistency

set_option autoImplicit false

open P0EFTJanusSpectralIsotropyAlphaRatio

/-- Spectral lock plus the bimetric throat identification `A=L`. -/
structure SpectralBimetricMatch where
  spectral : ThroatSpectralLock
  alphaEqualsGeometry :
    spectral.alphaSquaredLength = spectral.geometricLength

/--
If `A=L`, consistency fixes the dimensionless charge coefficient to
`c_q=1/8`.
-/
theorem alpha_equals_geometry_forces_charge_coefficient
    (s : SpectralBimetricMatch) :
    8 * s.spectral.chargeCoefficient = 1 := by
  have hRatio :=
    spectral_lock_fixes_alpha_ratio_fourth_power s.spectral
  rw [s.alphaEqualsGeometry] at hRatio
  have hLengthNonzero : s.spectral.geometricLength ^ 4 ≠ 0 :=
    pow_ne_zero 4 (ne_of_gt s.spectral.geometricLengthPositive)
  have hFactor :
      s.spectral.geometricLength ^ 4 *
        (64 * s.spectral.chargeCoefficient ^ 2 - 1) = 0 := by
    nlinarith [hRatio]
  have hCoefficientSquare :
      64 * s.spectral.chargeCoefficient ^ 2 = 1 := by
    have hDifference :=
      (mul_eq_zero.mp hFactor).resolve_left hLengthNonzero
    linarith
  have hRootFactor :
      (8 * s.spectral.chargeCoefficient - 1) *
        (8 * s.spectral.chargeCoefficient + 1) = 0 := by
    nlinarith [hCoefficientSquare]
  rcases mul_eq_zero.mp hRootFactor with hPositiveRoot | hNegativeRoot
  · linarith
  · have hStrictPositive :
        0 < 8 * s.spectral.chargeCoefficient + 1 := by
      nlinarith [s.spectral.chargeCoefficientPositive]
    exact False.elim ((ne_of_gt hStrictPositive) hNegativeRoot)

/-- In ordinary notation the coefficient is exactly `1/8`. -/
theorem charge_coefficient_eq_one_eighth
    (s : SpectralBimetricMatch) :
    s.spectral.chargeCoefficient = 1 / 8 := by
  have h := alpha_equals_geometry_forces_charge_coefficient s
  norm_num at h ⊢
  linarith

/--
Conversely, the computed coefficient `1/8` turns the spectral fourth-power law
into `A^4=L^4`, and positivity recovers the bimetric equality `A=L`.
-/
theorem one_eighth_coefficient_recovers_alpha_equals_geometry
    (s : ThroatSpectralLock)
    (hCoefficient : s.chargeCoefficient = 1 / 8) :
    s.alphaSquaredLength = s.geometricLength := by
  have hRatio := spectral_lock_fixes_alpha_ratio_fourth_power s
  rw [hCoefficient] at hRatio
  norm_num at hRatio
  have hFourth :
      s.alphaSquaredLength ^ 4 = s.geometricLength ^ 4 := by
    nlinarith [hRatio]
  have hSquare :
      s.alphaSquaredLength ^ 2 = s.geometricLength ^ 2 := by
    have hFactor :
        (s.alphaSquaredLength ^ 2 - s.geometricLength ^ 2) *
          (s.alphaSquaredLength ^ 2 + s.geometricLength ^ 2) = 0 := by
      nlinarith [hFourth]
    rcases mul_eq_zero.mp hFactor with hDifference | hSum
    · linarith
    · have hPositive :
          0 < s.alphaSquaredLength ^ 2 + s.geometricLength ^ 2 := by
        positivity
      exact False.elim ((ne_of_gt hPositive) hSum)
  have hFactor :
      (s.alphaSquaredLength - s.geometricLength) *
        (s.alphaSquaredLength + s.geometricLength) = 0 := by
    nlinarith [hSquare]
  rcases mul_eq_zero.mp hFactor with hDifference | hSum
  · linarith
  · have hPositive :
        0 < s.alphaSquaredLength + s.geometricLength :=
      add_pos s.alphaSquaredLengthPositive s.geometricLengthPositive
    exact False.elim ((ne_of_gt hPositive) hSum)

/-- The new quantitative target for Program A/D compatibility. -/
structure ChargeCoefficientDerivationStatus where
  canonicalThroatConnectionNormalized : Prop
  auxiliaryMetricRelationDerived : Prop
  firstSpectralModeIdentified : Prop
  chargeOperatorRenormalized : Prop
  coefficientComputedAsOneEighth : Prop
  bimetricRadiusMatchRecovered : Prop


def chargeCoefficientCompatibilityClosed
    (s : ChargeCoefficientDerivationStatus) : Prop :=
  s.canonicalThroatConnectionNormalized /\
  s.auxiliaryMetricRelationDerived /\
  s.firstSpectralModeIdentified /\
  s.chargeOperatorRenormalized /\
  s.coefficientComputedAsOneEighth /\
  s.bimetricRadiusMatchRecovered

end P0EFTJanusSpectralBimetricConsistency
end JanusFormal

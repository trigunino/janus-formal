import Mathlib

namespace JanusFormal
namespace P0EFTJanusDiracBimetricPrimitiveSelection

set_option autoImplicit false

/--
General monopole-magnitude version of the Dirac/LL lock.  The round-sphere first
nonzero gap obeys `gap^2 * L^2 = m + 1`.
-/
structure GeneralMonopoleRadiusLock where
  monopoleMagnitude : ℝ
  sphereRadius : ℝ
  sphereGapSquared : ℝ
  llChargeUnit : ℝ
  alphaSquaredLength : ℝ
  monopoleMagnitudeNonnegative : 0 ≤ monopoleMagnitude
  sphereRadiusPositive : 0 < sphereRadius
  sphereGapPositive : 0 < sphereGapSquared
  llChargePositive : 0 < llChargeUnit
  alphaPositive : 0 < alphaSquaredLength
  sphereGapLaw :
    sphereGapSquared * sphereRadius ^ 2 = monopoleMagnitude + 1
  oneEighthChargeLaw :
    8 * llChargeUnit = sphereGapSquared
  primitiveLLFluxLaw :
    16 * llChargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- Squared spectral/LL radius relation. -/
theorem general_radius_fourth_power_law
    (s : GeneralMonopoleRadiusLock) :
    (s.monopoleMagnitude + 1) ^ 2 * s.alphaSquaredLength ^ 4 =
      4 * s.sphereRadius ^ 4 := by
  have hGapSquared :
      s.sphereGapSquared ^ 2 * s.sphereRadius ^ 4 =
        (s.monopoleMagnitude + 1) ^ 2 := by
    calc
      s.sphereGapSquared ^ 2 * s.sphereRadius ^ 4 =
          (s.sphereGapSquared * s.sphereRadius ^ 2) ^ 2 := by ring
      _ = (s.monopoleMagnitude + 1) ^ 2 := by rw [s.sphereGapLaw]
  have hChargeSquared :
      64 * s.llChargeUnit ^ 2 = s.sphereGapSquared ^ 2 := by
    nlinarith [s.oneEighthChargeLaw]
  have hFluxScaled :
      4 * s.sphereGapSquared ^ 2 * s.alphaSquaredLength ^ 4 = 16 := by
    nlinarith [s.primitiveLLFluxLaw, hChargeSquared]
  nlinarith [hGapSquared, hFluxScaled,
    sq_nonneg s.sphereRadius, sq_nonneg s.alphaSquaredLength]

/--
If the exact-solution length equals the sphere throat radius, the monopole
magnitude is forced to one.
-/
theorem bimetric_radius_match_selects_primitive_monopole
    (s : GeneralMonopoleRadiusLock)
    (hMatch : s.alphaSquaredLength = s.sphereRadius) :
    s.monopoleMagnitude = 1 := by
  have hFourth := general_radius_fourth_power_law s
  rw [hMatch] at hFourth
  have hRadiusFourthPositive : 0 < s.sphereRadius ^ 4 :=
    pow_pos s.sphereRadiusPositive 4
  have hMagnitudeSquare :
      (s.monopoleMagnitude + 1) ^ 2 = 4 := by
    have hFactor :
        ((s.monopoleMagnitude + 1) ^ 2 - 4) *
          s.sphereRadius ^ 4 = 0 := by
      nlinarith [hFourth]
    have hRadiusNonzero : s.sphereRadius ^ 4 ≠ 0 :=
      ne_of_gt hRadiusFourthPositive
    have hDifference :=
      (mul_eq_zero.mp hFactor).resolve_right hRadiusNonzero
    linarith
  have hMagnitudePlusPositive : 0 < s.monopoleMagnitude + 1 := by
    linarith [s.monopoleMagnitudeNonnegative]
  nlinarith [hMagnitudeSquare, hMagnitudePlusPositive]

/--
Conversely, in the primitive sector the positive branch fixes `A=L`.
-/
theorem primitive_monopole_recovers_bimetric_radius_match
    (s : GeneralMonopoleRadiusLock)
    (hPrimitive : s.monopoleMagnitude = 1) :
    s.alphaSquaredLength = s.sphereRadius := by
  have hFourth := general_radius_fourth_power_law s
  rw [hPrimitive] at hFourth
  norm_num at hFourth
  have hSquares :
      s.alphaSquaredLength ^ 2 = s.sphereRadius ^ 2 := by
    have hFactor :
        (s.alphaSquaredLength ^ 2 - s.sphereRadius ^ 2) *
          (s.alphaSquaredLength ^ 2 + s.sphereRadius ^ 2) = 0 := by
      nlinarith [hFourth]
    rcases mul_eq_zero.mp hFactor with hDifference | hSum
    · linarith
    · have hPositive :
          0 < s.alphaSquaredLength ^ 2 + s.sphereRadius ^ 2 := by
        positivity
      exact False.elim ((ne_of_gt hPositive) hSum)
  have hRootFactor :
      (s.alphaSquaredLength - s.sphereRadius) *
        (s.alphaSquaredLength + s.sphereRadius) = 0 := by
    nlinarith [hSquares]
  rcases mul_eq_zero.mp hRootFactor with hDifference | hSum
  · linarith
  · have hPositive :
        0 < s.alphaSquaredLength + s.sphereRadius :=
      add_pos s.alphaPositive s.sphereRadiusPositive
    exact False.elim ((ne_of_gt hPositive) hSum)

/-- Primitive topology and bimetric matching are equivalent inside this lock. -/
theorem primitive_iff_bimetric_radius_match
    (s : GeneralMonopoleRadiusLock) :
    s.monopoleMagnitude = 1 ↔
      s.alphaSquaredLength = s.sphereRadius := by
  constructor
  · exact primitive_monopole_recovers_bimetric_radius_match s
  · exact bimetric_radius_match_selects_primitive_monopole s

end P0EFTJanusDiracBimetricPrimitiveSelection
end JanusFormal

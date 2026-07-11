import Mathlib

namespace JanusFormal
namespace P0EFTJanusDiracSpectralGeometryLock

set_option autoImplicit false

/--
Primitive-monopole Dirac data on the product throat
`S2_L x S1_(L*T)`.

At half holonomy, the lowest circle momentum has cleared square `pi^2`, while
the first nonzero primitive-monopole Dirac level on `S2` has cleared square `2`.
The LL charge is locked to one eighth of the sphere Dirac gap.
-/
structure PrimitiveDiracThroatLock where
  sphereRadius : ℝ
  circleModulus : ℝ
  circleRadius : ℝ
  piConstant : ℝ
  sphereGapSquared : ℝ
  circleGapSquared : ℝ
  llChargeUnit : ℝ
  alphaSquaredLength : ℝ
  sphereRadiusPositive : 0 < sphereRadius
  circleModulusPositive : 0 < circleModulus
  circleRadiusPositive : 0 < circleRadius
  piConstantPositive : 0 < piConstant
  sphereGapPositive : 0 < sphereGapSquared
  circleGapPositive : 0 < circleGapSquared
  llChargePositive : 0 < llChargeUnit
  alphaPositive : 0 < alphaSquaredLength
  primitiveSphereGapLaw :
    sphereGapSquared * sphereRadius ^ 2 = 2
  halfHolonomyCircleGapLaw :
    circleGapSquared * sphereRadius ^ 2 * circleModulus ^ 2 =
      piConstant ^ 2
  spectralIsotropy :
    sphereGapSquared = circleGapSquared
  circleRadiusLaw :
    2 * piConstant * circleRadius = sphereRadius * circleModulus
  chargeIsOneEighthDiracGap :
    8 * llChargeUnit = sphereGapSquared
  primitiveLLFluxLaw :
    16 * llChargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- Dirac spectral isotropy fixes `2*T^2 = pi^2`. -/
theorem dirac_isotropy_fixes_circle_modulus
    (s : PrimitiveDiracThroatLock) :
    2 * s.circleModulus ^ 2 = s.piConstant ^ 2 := by
  have hCircle := s.halfHolonomyCircleGapLaw
  rw [← s.spectralIsotropy] at hCircle
  have hReassociated :
      (s.sphereGapSquared * s.sphereRadius ^ 2) *
          s.circleModulus ^ 2 = s.piConstant ^ 2 := by
    simpa [mul_assoc] using hCircle
  rw [s.primitiveSphereGapLaw] at hReassociated
  exact hReassociated

/-- The compact circle radius obeys `8*R1^2 = L^2`. -/
theorem circle_radius_to_sphere_radius_ratio
    (s : PrimitiveDiracThroatLock) :
    8 * s.circleRadius ^ 2 = s.sphereRadius ^ 2 := by
  have hCircleSquared :
      4 * s.piConstant ^ 2 * s.circleRadius ^ 2 =
        s.sphereRadius ^ 2 * s.circleModulus ^ 2 := by
    nlinarith [s.circleRadiusLaw]
  have hModulus := dirac_isotropy_fixes_circle_modulus s
  have hFactor :
      s.circleModulus ^ 2 *
        (8 * s.circleRadius ^ 2 - s.sphereRadius ^ 2) = 0 := by
    nlinarith [hCircleSquared, hModulus]
  have hModulusNonzero : s.circleModulus ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt s.circleModulusPositive)
  have hDifference :
      8 * s.circleRadius ^ 2 - s.sphereRadius ^ 2 = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hModulusNonzero
  linarith

/-- The one-eighth gap normalization gives `4*q*L^2 = 1`. -/
theorem charge_sphere_radius_law
    (s : PrimitiveDiracThroatLock) :
    4 * s.llChargeUnit * s.sphereRadius ^ 2 = 1 := by
  have hGap := s.primitiveSphereGapLaw
  have hCharge := s.chargeIsOneEighthDiracGap
  nlinarith

/-- The positive primitive LL branch gives `4*q*A^2 = 1`. -/
theorem charge_alpha_radius_law
    (s : PrimitiveDiracThroatLock) :
    4 * s.llChargeUnit * s.alphaSquaredLength ^ 2 = 1 := by
  let x : ℝ := 4 * s.llChargeUnit * s.alphaSquaredLength ^ 2
  have hSquare : x ^ 2 = 1 := by
    dsimp [x]
    calc
      (4 * s.llChargeUnit * s.alphaSquaredLength ^ 2) ^ 2 =
          16 * s.llChargeUnit ^ 2 * s.alphaSquaredLength ^ 4 := by ring
      _ = 1 := s.primitiveLLFluxLaw
  have hPositive : 0 < x := by
    dsimp [x]
    exact mul_pos
      (mul_pos (by norm_num) s.llChargePositive)
      (pow_pos s.alphaPositive 2)
  have hFactor : (x - 1) * (x + 1) = 0 := by
    nlinarith [hSquare]
  rcases mul_eq_zero.mp hFactor with hMinus | hPlus
  · dsimp [x] at hMinus ⊢
    linarith
  · have hSumPositive : 0 < x + 1 := by linarith
    exact False.elim ((ne_of_gt hSumPositive) hPlus)

/--
The primitive monopole gap, the LL auxiliary normalization and primitive flux
force the exact-solution length to equal the `S2` throat radius.
-/
theorem alpha_equals_sphere_radius
    (s : PrimitiveDiracThroatLock) :
    s.alphaSquaredLength = s.sphereRadius := by
  have hAlpha := charge_alpha_radius_law s
  have hSphere := charge_sphere_radius_law s
  have hChargeNonzero : 4 * s.llChargeUnit ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt s.llChargePositive)
  have hSquares :
      s.alphaSquaredLength ^ 2 = s.sphereRadius ^ 2 := by
    have hFactor :
        (4 * s.llChargeUnit) *
          (s.alphaSquaredLength ^ 2 - s.sphereRadius ^ 2) = 0 := by
      nlinarith [hAlpha, hSphere]
    have hDifference :=
      (mul_eq_zero.mp hFactor).resolve_left hChargeNonzero
    linarith
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

/--
The previously observed `1/(2*sqrt(2))` ratio belongs to the compact circle
radius, not to alpha relative to the `S2` throat radius.
-/
theorem corrected_circle_alpha_ratio
    (s : PrimitiveDiracThroatLock) :
    8 * s.circleRadius ^ 2 = s.alphaSquaredLength ^ 2 := by
  rw [alpha_equals_sphere_radius s]
  exact circle_radius_to_sphere_radius_ratio s

/--
This package is conditional on the spectral formula, half-holonomy vacuum and
the one-eighth LL normalization.  Those are the next operator/QFT theorems, not
free numerical assumptions to hide in the final prediction.
-/
structure DiracGeometryClosureStatus where
  primitiveMonopoleDerived : Prop
  twistedSphereDiracSpectrumDerived : Prop
  halfHolonomyVacuumDerived : Prop
  productSpectrumPairingDerived : Prop
  oneEighthChargeNormalizationDerived : Prop
  spectralIsotropyDerived : Prop
  alphaSphereRadiusEqualityDerived : Prop
  compactCircleRatioDerived : Prop


def diracGeometryClosure
    (s : DiracGeometryClosureStatus) : Prop :=
  s.primitiveMonopoleDerived /\
  s.twistedSphereDiracSpectrumDerived /\
  s.halfHolonomyVacuumDerived /\
  s.productSpectrumPairingDerived /\
  s.oneEighthChargeNormalizationDerived /\
  s.spectralIsotropyDerived /\
  s.alphaSphereRadiusEqualityDerived /\
  s.compactCircleRatioDerived

end P0EFTJanusDiracSpectralGeometryLock
end JanusFormal

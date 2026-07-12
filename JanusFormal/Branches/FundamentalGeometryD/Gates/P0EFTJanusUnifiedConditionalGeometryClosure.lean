import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusSpectralMismatchVacuum

namespace JanusFormal
namespace P0EFTJanusUnifiedConditionalGeometryClosure

set_option autoImplicit false

open P0EFTJanusSpectralMismatchVacuum

/--
One coherent conditional data set joining the throat spectrum, the LL flux and
the cosmological exact-solution scale.
-/
structure UnifiedConditionalGeometry where
  geometricLength : ℝ
  circleModulus : ℝ
  piConstant : ℝ
  sphereFirstEigenvalue : ℝ
  llChargeUnit : ℝ
  spectralChargeCoefficient : ℝ
  alphaSquaredLength : ℝ
  mismatchWeight : ℝ
  geometricLengthPositive : 0 < geometricLength
  circleModulusPositive : 0 < circleModulus
  piConstantPositive : 0 < piConstant
  sphereEigenvaluePositive : 0 < sphereFirstEigenvalue
  llChargeUnitPositive : 0 < llChargeUnit
  spectralCoefficientPositive : 0 < spectralChargeCoefficient
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  mismatchWeightPositive : 0 < mismatchWeight
  sphereModeLaw :
    sphereFirstEigenvalue * geometricLength ^ 2 = 2
  chargeFromSphereMode :
    llChargeUnit = spectralChargeCoefficient * sphereFirstEigenvalue
  spectralVacuumLaw :
    mismatchEnergy mismatchWeight circleModulus piConstant = 0
  primitiveThroatFluxLaw :
    16 * llChargeUnit ^ 2 * geometricLength ^ 4 = 1
  primitiveCosmologyFluxLaw :
    16 * llChargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- The positive primitive throat law has the unsquared form `4*q*L^2=1`. -/
theorem primitive_throat_flux_linearized
    (s : UnifiedConditionalGeometry) :
    4 * s.llChargeUnit * s.geometricLength ^ 2 = 1 := by
  let x : ℝ := 4 * s.llChargeUnit * s.geometricLength ^ 2
  have hSquare : x ^ 2 = 1 := by
    dsimp [x]
    calc
      (4 * s.llChargeUnit * s.geometricLength ^ 2) ^ 2 =
          16 * s.llChargeUnit ^ 2 * s.geometricLength ^ 4 := by ring
      _ = 1 := s.primitiveThroatFluxLaw
  have hPositive : 0 < x := by
    dsimp [x]
    exact mul_pos
      (mul_pos (by norm_num) s.llChargeUnitPositive)
      (pow_pos s.geometricLengthPositive 2)
  have hFactor : (x - 1) * (x + 1) = 0 := by
    nlinarith [hSquare]
  rcases mul_eq_zero.mp hFactor with hMinus | hPlus
  · dsimp [x] at hMinus ⊢
    linarith
  · have hSumPositive : 0 < x + 1 := by linarith
    exact False.elim ((ne_of_gt hSumPositive) hPlus)

/-- The sphere gap and LL normalization compute `c_q=1/8`. -/
theorem unified_geometry_fixes_charge_coefficient
    (s : UnifiedConditionalGeometry) :
    8 * s.spectralChargeCoefficient = 1 := by
  have hLinear := primitive_throat_flux_linearized s
  have hChargeLength :
      s.llChargeUnit * s.geometricLength ^ 2 =
        2 * s.spectralChargeCoefficient := by
    calc
      s.llChargeUnit * s.geometricLength ^ 2 =
          (s.spectralChargeCoefficient * s.sphereFirstEigenvalue) *
            s.geometricLength ^ 2 := by rw [s.chargeFromSphereMode]
      _ = s.spectralChargeCoefficient *
          (s.sphereFirstEigenvalue * s.geometricLength ^ 2) := by ring
      _ = 2 * s.spectralChargeCoefficient := by
        rw [s.sphereModeLaw]
        ring
  nlinarith [hLinear, hChargeLength]

/-- The same primitive charge on the throat and cosmology forces `A=L`. -/
theorem unified_flux_fixes_alpha_equals_geometry
    (s : UnifiedConditionalGeometry) :
    s.alphaSquaredLength = s.geometricLength := by
  have hChargeNonzero : 16 * s.llChargeUnit ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (ne_of_gt s.llChargeUnitPositive))
  have hDifference :
      16 * s.llChargeUnit ^ 2 *
        (s.alphaSquaredLength ^ 4 - s.geometricLength ^ 4) = 0 := by
    nlinarith [s.primitiveCosmologyFluxLaw, s.primitiveThroatFluxLaw]
  have hFourthDifference :
      s.alphaSquaredLength ^ 4 - s.geometricLength ^ 4 = 0 :=
    (mul_eq_zero.mp hDifference).resolve_left hChargeNonzero
  have hFourth :
      s.alphaSquaredLength ^ 4 = s.geometricLength ^ 4 := by
    linarith
  have hSquareFactor :
      (s.alphaSquaredLength ^ 2 - s.geometricLength ^ 2) *
        (s.alphaSquaredLength ^ 2 + s.geometricLength ^ 2) = 0 := by
    nlinarith [hFourth]
  have hSquare :
      s.alphaSquaredLength ^ 2 = s.geometricLength ^ 2 := by
    rcases mul_eq_zero.mp hSquareFactor with hDiff | hSum
    · linarith
    · have hPositive :
          0 < s.alphaSquaredLength ^ 2 + s.geometricLength ^ 2 :=
        add_pos
          (pow_pos s.alphaSquaredLengthPositive 2)
          (pow_pos s.geometricLengthPositive 2)
      exact False.elim ((ne_of_gt hPositive) hSum)
  have hLinearFactor :
      (s.alphaSquaredLength - s.geometricLength) *
        (s.alphaSquaredLength + s.geometricLength) = 0 := by
    nlinarith [hSquare]
  rcases mul_eq_zero.mp hLinearFactor with hDiff | hSum
  · linarith
  · have hPositive :
        0 < s.alphaSquaredLength + s.geometricLength :=
      add_pos s.alphaSquaredLengthPositive s.geometricLengthPositive
    exact False.elim ((ne_of_gt hPositive) hSum)

/-- The positive mismatch vacuum fixes the circle modulus squared. -/
theorem unified_geometry_fixes_circle_modulus
    (s : UnifiedConditionalGeometry) :
    s.circleModulus ^ 2 = 2 * s.piConstant ^ 2 := by
  exact
    (mismatch_energy_zero_iff_isotropy
      s.mismatchWeight s.circleModulus s.piConstant
      s.mismatchWeightPositive).mp s.spectralVacuumLaw

/-- Terminal conditional Program D result. -/
theorem unified_conditional_geometry_spectrum
    (s : UnifiedConditionalGeometry) :
    (s.circleModulus ^ 2 = 2 * s.piConstant ^ 2) /\
    (8 * s.spectralChargeCoefficient = 1) /\
    (s.alphaSquaredLength = s.geometricLength) := by
  exact ⟨unified_geometry_fixes_circle_modulus s,
    unified_geometry_fixes_charge_coefficient s,
    unified_flux_fixes_alpha_equals_geometry s⟩

/--
Only the physical derivation of the common charge, spectral mismatch term and
absolute geometric scale remains; their algebraic consequences are now unique.
-/
structure UnifiedPhysicalDerivationStatus where
  commonThroatAndCosmologyChargeDerived : Prop
  primitiveFluxSectorDerived : Prop
  spectralMismatchTermDerived : Prop
  positiveMismatchWeightDerived : Prop
  sphereModeChargeMapDerived : Prop
  absoluteGeometryScaleDerived : Prop
  noObservedScaleImported : Prop


def unifiedPhysicalDerivationClosed
    (s : UnifiedPhysicalDerivationStatus) : Prop :=
  s.commonThroatAndCosmologyChargeDerived /\
  s.primitiveFluxSectorDerived /\
  s.spectralMismatchTermDerived /\
  s.positiveMismatchWeightDerived /\
  s.sphereModeChargeMapDerived /\
  s.absoluteGeometryScaleDerived /\
  s.noObservedScaleImported

end P0EFTJanusUnifiedConditionalGeometryClosure
end JanusFormal

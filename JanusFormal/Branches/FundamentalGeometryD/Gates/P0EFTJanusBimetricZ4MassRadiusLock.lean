import Mathlib

namespace JanusFormal
namespace P0EFTJanusBimetricZ4MassRadiusLock

set_option autoImplicit false

/--
Compatibility data for the first integer periodic/quarter-holonomy determinant
candidate. The stable root is `exp(-m*L*T)=1/3`, encoded as

`m * L * T = log 3`.

The earlier Dirac/LL radius lock requires the dimensionless throat modulus
`T^2 = 2*pi^2` and `A=L`.
-/
structure OneFiveMassRadiusLock where
  physicalMass : ℝ
  geometricLength : ℝ
  circleModulus : ℝ
  alphaSquaredLength : ℝ
  physicalMassPositive : 0 < physicalMass
  geometricLengthPositive : 0 < geometricLength
  circleModulusPositive : 0 < circleModulus
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  determinantMinimum :
    physicalMass * geometricLength * circleModulus = Real.log 3
  spectralModulus :
    circleModulus ^ 2 = 2 * Real.pi ^ 2
  alphaEqualsGeometry :
    alphaSquaredLength = geometricLength

/-- The determinant minimum and spectral modulus fix the dimensionless mass. -/
theorem one_five_dimensionless_mass_target
    (s : OneFiveMassRadiusLock) :
    2 * Real.pi ^ 2 *
        (s.physicalMass * s.geometricLength) ^ 2 =
      (Real.log 3) ^ 2 := by
  have hSquared := congrArg (fun value : ℝ => value ^ 2)
    s.determinantMinimum
  calc
    2 * Real.pi ^ 2 *
        (s.physicalMass * s.geometricLength) ^ 2 =
      (s.physicalMass * s.geometricLength) ^ 2 *
        s.circleModulus ^ 2 := by
          rw [s.spectralModulus]
          ring
    _ = (s.physicalMass * s.geometricLength *
          s.circleModulus) ^ 2 := by ring
    _ = (Real.log 3) ^ 2 := hSquared

/-- In exact-solution notation, the same law is a mass-radius target for `A`. -/
theorem one_five_physical_mass_alpha_target
    (s : OneFiveMassRadiusLock) :
    2 * Real.pi ^ 2 *
        (s.physicalMass * s.alphaSquaredLength) ^ 2 =
      (Real.log 3) ^ 2 := by
  rw [s.alphaEqualsGeometry]
  exact one_five_dimensionless_mass_target s

/-- The compatible determinant mass is lighter than `1/sqrt(2)` in units of `L`. -/
theorem one_five_mass_is_strictly_light
    (s : OneFiveMassRadiusLock) :
    (s.physicalMass * s.geometricLength) ^ 2 < 1 / 2 := by
  have hTarget := one_five_dimensionless_mass_target s
  have hLogPositive : 0 < Real.log 3 :=
    Real.log_pos (by norm_num)
  have hLogUpper : Real.log 3 < 2 := by
    have h := Real.log_lt_sub_one_of_pos
      (x := (3 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hLogSquare : (Real.log 3) ^ 2 < 4 := by
    nlinarith [sq_nonneg (Real.log 3)]
  have hPiSquare : 4 ≤ Real.pi ^ 2 := by
    nlinarith [Real.two_le_pi, sq_nonneg (Real.pi - 2)]
  have hMassSquare :
      0 ≤ (s.physicalMass * s.geometricLength) ^ 2 := sq_nonneg _
  have hProductLower :
      4 * (s.physicalMass * s.geometricLength) ^ 2 ≤
        Real.pi ^ 2 *
          (s.physicalMass * s.geometricLength) ^ 2 :=
    mul_le_mul_of_nonneg_right hPiSquare hMassSquare
  nlinarith [hTarget, hLogSquare, hProductLower, hLogPositive]

/-- The first positive primitive-monopole sphere mass `(mL)^2=2` is incompatible. -/
theorem first_sphere_dirac_mass_cannot_satisfy_one_five_lock
    (s : OneFiveMassRadiusLock)
    (hFirstSphereMass :
      (s.physicalMass * s.geometricLength) ^ 2 = 2) : False := by
  have hTarget := one_five_dimensionless_mass_target s
  rw [hFirstSphereMass] at hTarget
  have hLogPositive : 0 < Real.log 3 :=
    Real.log_pos (by norm_num)
  have hLogUpper : Real.log 3 < 2 := by
    have h := Real.log_lt_sub_one_of_pos
      (x := (3 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hLogSquare : (Real.log 3) ^ 2 < 4 := by
    nlinarith [sq_nonneg (Real.log 3)]
  have hPiSquare : 4 ≤ Real.pi ^ 2 := by
    nlinarith [Real.two_le_pi, sq_nonneg (Real.pi - 2)]
  nlinarith [hTarget, hLogSquare, hPiSquare, hLogPositive]

/--
A bimetric interaction parametrization of the physical mass,
`m_FP^2 = mu_B^2 * B_FP`.
-/
structure FierzPauliInteractionLock extends OneFiveMassRadiusLock where
  interactionMassSquared : ℝ
  fpCombination : ℝ
  interactionMassSquaredPositive : 0 < interactionMassSquared
  fpCombinationPositive : 0 < fpCombination
  fpMassLaw :
    physicalMass ^ 2 = interactionMassSquared * fpCombination

/-- The determinant mechanism fixes one dimensionless bimetric interaction combination. -/
theorem bimetric_interaction_alpha_target
    (s : FierzPauliInteractionLock) :
    2 * Real.pi ^ 2 * s.interactionMassSquared *
        s.fpCombination * s.alphaSquaredLength ^ 2 =
      (Real.log 3) ^ 2 := by
  have hTarget := one_five_physical_mass_alpha_target
    s.toOneFiveMassRadiusLock
  calc
    2 * Real.pi ^ 2 * s.interactionMassSquared *
        s.fpCombination * s.alphaSquaredLength ^ 2 =
      2 * Real.pi ^ 2 * s.physicalMass ^ 2 *
        s.alphaSquaredLength ^ 2 := by
          rw [s.fpMassLaw]
          ring
    _ = 2 * Real.pi ^ 2 *
        (s.physicalMass * s.alphaSquaredLength) ^ 2 := by ring
    _ = (Real.log 3) ^ 2 := hTarget

/--
The result is a sharp target, not an absolute prediction: if `m_FP` is itself a
free dimensionful parameter, the equation merely transports that freedom into
`A`. A no-fit radius requires deriving the bimetric mass scale microscopically.
-/
structure BimetricMassScaleDerivationStatus where
  determinantWeightTwoToTenDerived : Prop
  stableOneThirdRootDerived : Prop
  spectralModulusDerived : Prop
  fpMassCombinationDerived : Prop
  interactionMassScaleDerived : Prop
  massRadiusTargetDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaDerived : Prop


def bimetricMassScaleDerivationClosed
    (s : BimetricMassScaleDerivationStatus) : Prop :=
  s.determinantWeightTwoToTenDerived /\
  s.stableOneThirdRootDerived /\
  s.spectralModulusDerived /\
  s.fpMassCombinationDerived /\
  s.interactionMassScaleDerived /\
  s.massRadiusTargetDerived /\
  s.noObservedScaleImported /\
  s.absoluteAlphaDerived

end P0EFTJanusBimetricZ4MassRadiusLock
end JanusFormal

import Mathlib

namespace JanusFormal
namespace P0EFTJanusPrimitiveMonopoleDiracSpectrum

set_option autoImplicit false

/-- Squared `S2` Dirac eigenvalue numerator for monopole magnitude `q` and radial level `p`.

The standard twisted-sphere spectrum has

`lambda_p^2 L^2 = p * (p + q)`,

with `p = 0,1,...` and degeneracy `q + 2p`. Here `q` is the positive magnitude
of the integral monopole charge.
-/
def sphereDiracSquaredNumerator (chargeMagnitude level : ℕ) : ℕ :=
  level * (level + chargeMagnitude)

/-- Degeneracy of the corresponding sphere level. -/
def sphereDiracDegeneracy (chargeMagnitude level : ℕ) : ℕ :=
  chargeMagnitude + 2 * level

/-- The zero sphere level is always a zero mode. -/
@[simp] theorem sphere_zero_level_is_zero
    (chargeMagnitude : ℕ) :
    sphereDiracSquaredNumerator chargeMagnitude 0 = 0 := by
  simp [sphereDiracSquaredNumerator]

/-- Its degeneracy is the monopole charge magnitude, matching the index count. -/
@[simp] theorem sphere_zero_mode_degeneracy
    (chargeMagnitude : ℕ) :
    sphereDiracDegeneracy chargeMagnitude 0 = chargeMagnitude := by
  simp [sphereDiracDegeneracy]

/-- For primitive charge, the first positive sphere level has squared numerator two. -/
@[simp] theorem primitive_first_positive_sphere_level :
    sphereDiracSquaredNumerator 1 1 = 2 := by
  norm_num [sphereDiracSquaredNumerator]

/-- For primitive charge, that first positive sphere level has degeneracy three. -/
@[simp] theorem primitive_first_positive_sphere_degeneracy :
    sphereDiracDegeneracy 1 1 = 3 := by
  norm_num [sphereDiracDegeneracy]

/-- Every strictly positive level has positive squared eigenvalue numerator when charge is positive. -/
theorem positive_level_has_positive_sphere_numerator
    (chargeMagnitude level : ℕ)
    (hCharge : 0 < chargeMagnitude)
    (hLevel : 0 < level) :
    0 < sphereDiracSquaredNumerator chargeMagnitude level := by
  unfold sphereDiracSquaredNumerator
  exact Nat.mul_pos hLevel (by omega)

/-- Dimensionless squared circle momentum for periodic spin structure. -/
noncomputable def periodicCircleSquared
    (piConstant circleModulus : ℝ) (mode : ℤ) : ℝ :=
  (2 * piConstant * (mode : ℝ) / circleModulus) ^ 2

/-- Dimensionless squared circle momentum for antiperiodic spin structure. -/
noncomputable def antiperiodicCircleSquared
    (piConstant circleModulus : ℝ) (mode : ℤ) : ℝ :=
  (2 * piConstant * ((mode : ℝ) + 1 / 2) / circleModulus) ^ 2

/-- Periodic zero momentum vanishes. -/
@[simp] theorem periodic_zero_momentum
    (piConstant circleModulus : ℝ) :
    periodicCircleSquared piConstant circleModulus 0 = 0 := by
  simp [periodicCircleSquared]

/-- The first nonzero periodic circle pair has squared momentum `(2*pi/T)^2`. -/
theorem periodic_first_circle_pair
    (piConstant circleModulus : ℝ) :
    periodicCircleSquared piConstant circleModulus 1 =
      (2 * piConstant / circleModulus) ^ 2 /\
    periodicCircleSquared piConstant circleModulus (-1) =
      (2 * piConstant / circleModulus) ^ 2 := by
  constructor <;> unfold periodicCircleSquared
  · norm_num
  · push_cast
    ring

/-- The lowest antiperiodic pair has squared momentum `(pi/T)^2`. -/
theorem antiperiodic_lowest_circle_pair
    (piConstant circleModulus : ℝ) :
    antiperiodicCircleSquared piConstant circleModulus 0 =
      (piConstant / circleModulus) ^ 2 /\
    antiperiodicCircleSquared piConstant circleModulus (-1) =
      (piConstant / circleModulus) ^ 2 := by
  constructor <;> unfold antiperiodicCircleSquared
  · ring
  · push_cast
    ring

/-- Dimensionless squared product eigenvalue for a sphere level and periodic circle mode. -/
noncomputable def periodicProductSquared
    (chargeMagnitude level : ℕ)
    (piConstant circleModulus : ℝ)
    (mode : ℤ) : ℝ :=
  (sphereDiracSquaredNumerator chargeMagnitude level : ℝ) +
    periodicCircleSquared piConstant circleModulus mode

/-- Primitive monopole, first positive sphere excitation and zero circle momentum. -/
theorem primitive_sphere_excitation_squared
    (piConstant circleModulus : ℝ) :
    periodicProductSquared 1 1 piConstant circleModulus 0 = 2 := by
  simp [periodicProductSquared]

/-- Primitive monopole zero mode with first periodic circle excitation. -/
theorem primitive_circle_excitation_squared
    (piConstant circleModulus : ℝ) :
    periodicProductSquared 1 0 piConstant circleModulus 1 =
      (2 * piConstant / circleModulus) ^ 2 := by
  simp [periodicProductSquared, periodicCircleSquared]

/-- The two first excitation families cross exactly at `T^2 = 2*pi^2`. -/
theorem first_excitation_crossing_iff
    (piConstant circleModulus : ℝ)
    (hCircle : circleModulus ≠ 0) :
    periodicProductSquared 1 1 piConstant circleModulus 0 =
        periodicProductSquared 1 0 piConstant circleModulus 1 ↔
      circleModulus ^ 2 = 2 * piConstant ^ 2 := by
  constructor
  · intro hCross
    rw [primitive_sphere_excitation_squared,
      primitive_circle_excitation_squared] at hCross
    field_simp [hCircle] at hCross
    nlinarith [hCross]
  · intro hModulus
    rw [primitive_sphere_excitation_squared,
      primitive_circle_excitation_squared]
    field_simp [hCircle]
    nlinarith [hModulus]

/-- At the crossing, the sphere family has degeneracy three. -/
def primitiveSphereFirstFamilyDegeneracy : ℕ :=
  sphereDiracDegeneracy 1 1

/-- The periodic circle family has two modes `m=+1` and `m=-1` built on one sphere zero mode. -/
def primitiveCircleFirstFamilyDegeneracy : ℕ := 2

@[simp] theorem first_family_degeneracies_are_three_and_two :
    primitiveSphereFirstFamilyDegeneracy = 3 /\
      primitiveCircleFirstFamilyDegeneracy = 2 := by
  norm_num [primitiveSphereFirstFamilyDegeneracy,
    primitiveCircleFirstFamilyDegeneracy,
    sphereDiracDegeneracy]

/-- Degeneracy-weighted balance of the two first families. -/
def firstFamilyWeightedBalance
    (piConstant circleModulus : ℝ) : Prop :=
  (primitiveSphereFirstFamilyDegeneracy : ℝ) * 2 =
    (primitiveCircleFirstFamilyDegeneracy : ℝ) *
      (2 * piConstant / circleModulus) ^ 2

/-- The simple `3:2` degeneracy proxy fixes `T^2 = 4*pi^2/3`. -/
theorem first_family_weighted_balance_iff
    (piConstant circleModulus : ℝ)
    (hCircle : circleModulus ≠ 0) :
    firstFamilyWeightedBalance piConstant circleModulus ↔
      3 * circleModulus ^ 2 = 4 * piConstant ^ 2 := by
  change
    (3 : ℝ) * 2 = 2 * (2 * piConstant / circleModulus) ^ 2 ↔
      3 * circleModulus ^ 2 = 4 * piConstant ^ 2
  constructor
  · intro hBalance
    field_simp [hCircle] at hBalance
    nlinarith [hBalance]
  · intro hModulus
    field_simp [hCircle]
    nlinarith [hModulus]

/--
The exact first-level spectrum therefore distinguishes two different candidate
moduli:

* equal eigenvalues: `T^2 = 2*pi^2`;
* degeneracy-weighted proxy: `3*T^2 = 4*pi^2`.

Neither condition is yet a determinant minimum. The full regularized effective
action must choose the physically relevant weighting.
-/
structure PrimitiveDiracSpectrumClosureStatus where
  monopoleDiracOperatorConstructed : Prop
  exactSphereSpectrumDerived : Prop
  circleSpinStructureSelected : Prop
  productSpectrumDerived : Prop
  zeroModesRegularized : Prop
  determinantWeightsComputed : Prop
  firstLevelApproximationValidated : Prop
  modulusMinimumDerived : Prop


def primitiveDiracSpectrumClosure
    (s : PrimitiveDiracSpectrumClosureStatus) : Prop :=
  s.monopoleDiracOperatorConstructed /\
  s.exactSphereSpectrumDerived /\
  s.circleSpinStructureSelected /\
  s.productSpectrumDerived /\
  s.zeroModesRegularized /\
  s.determinantWeightsComputed /\
  s.firstLevelApproximationValidated /\
  s.modulusMinimumDerived

end P0EFTJanusPrimitiveMonopoleDiracSpectrum
end JanusFormal

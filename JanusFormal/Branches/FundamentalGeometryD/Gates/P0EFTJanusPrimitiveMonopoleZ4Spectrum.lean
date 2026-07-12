import Mathlib

namespace JanusFormal
namespace P0EFTJanusPrimitiveMonopoleZ4Spectrum

set_option autoImplicit false

/--
For a primitive monopole `|n|=1`, the squared `S2` Dirac eigenvalue numerator
at Landau level `k` is `k*(k+1)`. The physical squared eigenvalue is this
numerator divided by the sphere radius squared.
-/
def primitiveSphereModeNumerator (mode : ℕ) : ℤ :=
  (mode : ℤ) * ((mode : ℤ) + 1)

/-- Degeneracy of the primitive-monopole sphere level. -/
def primitiveSphereModeDegeneracy (mode : ℕ) : ℕ :=
  1 + 2 * mode

@[simp] theorem primitive_sphere_zero_mode_numerator :
    primitiveSphereModeNumerator 0 = 0 := by
  norm_num [primitiveSphereModeNumerator]

@[simp] theorem primitive_sphere_zero_mode_degeneracy :
    primitiveSphereModeDegeneracy 0 = 1 := by
  norm_num [primitiveSphereModeDegeneracy]

@[simp] theorem primitive_sphere_first_excited_numerator :
    primitiveSphereModeNumerator 1 = 2 := by
  norm_num [primitiveSphereModeNumerator]

/-- Every positive sphere level has positive squared-eigenvalue numerator. -/
theorem positive_sphere_mode_has_positive_numerator
    (mode : ℕ)
    (hMode : 0 < mode) :
    0 < primitiveSphereModeNumerator mode := by
  have hModeInt : 0 < (mode : ℤ) := by
    exact_mod_cast hMode
  unfold primitiveSphereModeNumerator
  nlinarith

/-- Integer numerator of a circle momentum with quarter holonomy. -/
def quarterCircleMomentumNumerator (mode : ℤ) : ℤ :=
  4 * mode + 1

/-- Quarter holonomy removes the circle zero-momentum mode. -/
theorem quarter_circle_numerator_nonzero
    (mode : ℤ) :
    quarterCircleMomentumNumerator mode ≠ 0 := by
  unfold quarterCircleMomentumNumerator
  omega

/-- The square of every quarter-shifted momentum numerator is at least one. -/
theorem quarter_circle_square_at_least_one
    (mode : ℤ) :
    1 ≤ quarterCircleMomentumNumerator mode ^ 2 := by
  have hPositive :
      0 < quarterCircleMomentumNumerator mode ^ 2 :=
    sq_pos_of_ne_zero (quarter_circle_numerator_nonzero mode)
  omega

/--
After imposing the unweighted throat relation `T^2=2*pi^2`, the separated
primitive-monopole/quarter-holonomy spectrum obeys

`8*L^2*lambda^2 = 8*k*(k+1) + (4*m+1)^2`.

This definition is the dimensionless integer numerator on the right-hand side.
-/
def normalizedProductSpectrumNumerator
    (sphereMode : ℕ) (circleMode : ℤ) : ℤ :=
  8 * primitiveSphereModeNumerator sphereMode +
    quarterCircleMomentumNumerator circleMode ^ 2

/-- Every mode has normalized squared eigenvalue at least one. -/
theorem normalized_product_spectrum_at_least_one
    (sphereMode : ℕ) (circleMode : ℤ) :
    1 ≤ normalizedProductSpectrumNumerator sphereMode circleMode := by
  have hSphere :
      0 ≤ 8 * primitiveSphereModeNumerator sphereMode := by
    unfold primitiveSphereModeNumerator
    positivity
  have hCircle := quarter_circle_square_at_least_one circleMode
  unfold normalizedProductSpectrumNumerator
  linarith

/-- The unique lowest mode is the monopole zero mode with circle label zero. -/
theorem normalized_product_spectrum_eq_one_iff
    (sphereMode : ℕ) (circleMode : ℤ) :
    normalizedProductSpectrumNumerator sphereMode circleMode = 1 ↔
      sphereMode = 0 ∧ circleMode = 0 := by
  constructor
  · intro hSpectrum
    have hSphere :
        0 ≤ 8 * primitiveSphereModeNumerator sphereMode := by
      unfold primitiveSphereModeNumerator
      positivity
    have hCircle := quarter_circle_square_at_least_one circleMode
    have hSphereZero :
        8 * primitiveSphereModeNumerator sphereMode = 0 := by
      unfold normalizedProductSpectrumNumerator at hSpectrum
      linarith
    have hModeProduct :
        (sphereMode : ℤ) * ((sphereMode : ℤ) + 1) = 0 := by
      unfold primitiveSphereModeNumerator at hSphereZero
      nlinarith
    have hSphereModeZero : sphereMode = 0 := by
      rcases mul_eq_zero.mp hModeProduct with hMode | hSuccessor
      · exact_mod_cast hMode
      · have hNonnegative : 0 ≤ (sphereMode : ℤ) := by positivity
        omega
    subst sphereMode
    have hCircleSquare :
        quarterCircleMomentumNumerator circleMode ^ 2 = 1 := by
      simpa [normalizedProductSpectrumNumerator,
        primitiveSphereModeNumerator] using hSpectrum
    have hFactor :
        (quarterCircleMomentumNumerator circleMode - 1) *
          (quarterCircleMomentumNumerator circleMode + 1) = 0 := by
      nlinarith [hCircleSquare]
    have hCircleModeZero : circleMode = 0 := by
      rcases mul_eq_zero.mp hFactor with hPositiveRoot | hNegativeRoot
      · unfold quarterCircleMomentumNumerator at hPositiveRoot
        omega
      · unfold quarterCircleMomentumNumerator at hNegativeRoot
        omega
    exact ⟨rfl, hCircleModeZero⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [normalizedProductSpectrumNumerator,
      primitiveSphereModeNumerator, quarterCircleMomentumNumerator]

/-- The primitive `Z4` throat spectrum has a strictly positive unique gap. -/
theorem primitive_z4_throat_has_unique_positive_gap :
    normalizedProductSpectrumNumerator 0 0 = 1 /\
      ∀ sphereMode circleMode,
        normalizedProductSpectrumNumerator sphereMode circleMode = 1 →
          sphereMode = 0 ∧ circleMode = 0 := by
  constructor
  · norm_num [normalizedProductSpectrumNumerator,
      primitiveSphereModeNumerator, quarterCircleMomentumNumerator]
  · intro sphereMode circleMode h
    exact (normalized_product_spectrum_eq_one_iff sphereMode circleMode).mp h

/--
The algebraic spectrum is now explicit. The analytic theorem still has to
construct the twisted Dirac operator, prove that these are all eigenvalues with
the stated multiplicities, and control the determinant and eta regularization.
-/
structure PrimitiveMonopoleZ4AnalyticStatus where
  spinCBundleConstructed : Prop
  primitiveMonopoleConnectionConstructed : Prop
  quarterHolonomyDerivedFromPinLift : Prop
  selfAdjointProductDiracConstructed : Prop
  separatedSpectrumFormulaProved : Prop
  multiplicitiesProved : Prop
  spectralCompletenessProved : Prop
  heatKernelAndZetaContinuationDerived : Prop
  determinantAndEtaDerived : Prop


def primitiveMonopoleZ4AnalyticClosed
    (s : PrimitiveMonopoleZ4AnalyticStatus) : Prop :=
  s.spinCBundleConstructed /\
  s.primitiveMonopoleConnectionConstructed /\
  s.quarterHolonomyDerivedFromPinLift /\
  s.selfAdjointProductDiracConstructed /\
  s.separatedSpectrumFormulaProved /\
  s.multiplicitiesProved /\
  s.spectralCompletenessProved /\
  s.heatKernelAndZetaContinuationDerived /\
  s.determinantAndEtaDerived

end P0EFTJanusPrimitiveMonopoleZ4Spectrum
end JanusFormal

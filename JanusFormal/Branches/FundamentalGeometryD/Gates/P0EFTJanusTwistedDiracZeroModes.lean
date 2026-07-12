import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedDiracZeroModes

set_option autoImplicit false

/-- Squared eigenvalue in a separated product-mode model. -/
def productModeSquared
    (sphereEigenvalue circleMomentum : ℝ) : ℝ :=
  sphereEigenvalue ^ 2 + circleMomentum ^ 2

/-- A product mode is zero exactly when both separated factors are zero. -/
theorem product_mode_squared_zero_iff
    (sphereEigenvalue circleMomentum : ℝ) :
    productModeSquared sphereEigenvalue circleMomentum = 0 ↔
      sphereEigenvalue = 0 /\ circleMomentum = 0 := by
  constructor
  · intro hZero
    unfold productModeSquared at hZero
    have hSphere : 0 ≤ sphereEigenvalue ^ 2 := sq_nonneg _
    have hCircle : 0 ≤ circleMomentum ^ 2 := sq_nonneg _
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    norm_num [productModeSquared]

/-- Any nonzero circle momentum produces a strictly positive product eigenvalue. -/
theorem nonzero_circle_momentum_lifts_zero_mode
    (sphereEigenvalue circleMomentum : ℝ)
    (hCircle : circleMomentum ≠ 0) :
    0 < productModeSquared sphereEigenvalue circleMomentum := by
  unfold productModeSquared
  have hSphere : 0 ≤ sphereEigenvalue ^ 2 := sq_nonneg _
  have hCircleSquare : 0 < circleMomentum ^ 2 :=
    sq_pos_of_ne_zero hCircle
  nlinarith

/-- Chiral kernel dimensions and the monopole index relation on the sphere. -/
structure MonopoleDiracIndexData where
  positiveKernelDimension : ℕ
  negativeKernelDimension : ℕ
  index : ℤ
  firstChernNumber : ℤ
  indexFromKernels :
    index =
      (positiveKernelDimension : ℤ) -
        (negativeKernelDimension : ℤ)
  indexEqualsChernNumber : index = firstChernNumber

/-- A primitive nonzero Chern number forces a nontrivial chiral kernel. -/
theorem primitive_chern_number_forces_nontrivial_kernel
    (s : MonopoleDiracIndexData)
    (hPrimitive : s.firstChernNumber.natAbs = 1) :
    0 < s.positiveKernelDimension \/
      0 < s.negativeKernelDimension := by
  by_cases hPositive : 0 < s.positiveKernelDimension
  · exact Or.inl hPositive
  · right
    by_contra hNegative
    have hPositiveZero : s.positiveKernelDimension = 0 :=
      Nat.eq_zero_of_not_pos hPositive
    have hNegativeZero : s.negativeKernelDimension = 0 :=
      Nat.eq_zero_of_not_pos hNegative
    have hIndexZero : s.index = 0 := by
      rw [s.indexFromKernels, hPositiveZero, hNegativeZero]
      norm_num
    have hChernZero : s.firstChernNumber = 0 := by
      calc
        s.firstChernNumber = s.index := s.indexEqualsChernNumber.symm
        _ = 0 := hIndexZero
    rw [hChernZero] at hPrimitive
    norm_num at hPrimitive

/-- The two spin structures on the compact circle. -/
inductive CircleSpinStructure where
  | periodic
  | antiperiodic
  deriving DecidableEq, Repr

/-- Twice the dimensionless Kaluza--Klein momentum. -/
def circleMomentumNumerator
    (spin : CircleSpinStructure) (mode : ℤ) : ℤ :=
  match spin with
  | CircleSpinStructure.periodic => 2 * mode
  | CircleSpinStructure.antiperiodic => 2 * mode + 1

/-- The periodic circle has a zero-momentum mode. -/
@[simp] theorem periodic_zero_mode_numerator :
    circleMomentumNumerator CircleSpinStructure.periodic 0 = 0 := by
  rfl

/-- The antiperiodic circle has no zero-momentum mode. -/
theorem antiperiodic_numerator_nonzero
    (mode : ℤ) :
    circleMomentumNumerator
      CircleSpinStructure.antiperiodic mode ≠ 0 := by
  change 2 * mode + 1 ≠ 0
  omega

/-- Momentum after multiplication by a nonzero geometric scale factor. -/
def scaledCircleMomentum
    (scale : ℝ)
    (spin : CircleSpinStructure)
    (mode : ℤ) : ℝ :=
  scale * (circleMomentumNumerator spin mode : ℝ)

/-- Antiperiodic momentum remains nonzero after any nonzero scaling. -/
theorem antiperiodic_scaled_momentum_nonzero
    (scale : ℝ)
    (mode : ℤ)
    (hScale : scale ≠ 0) :
    scaledCircleMomentum scale
      CircleSpinStructure.antiperiodic mode ≠ 0 := by
  unfold scaledCircleMomentum
  apply mul_ne_zero hScale
  exact_mod_cast antiperiodic_numerator_nonzero mode

/-- A sphere zero mode survives in the periodic circle zero sector. -/
theorem periodic_circle_preserves_sphere_zero_mode
    (scale : ℝ) :
    productModeSquared 0
      (scaledCircleMomentum scale
        CircleSpinStructure.periodic 0) = 0 := by
  norm_num [scaledCircleMomentum, circleMomentumNumerator,
    productModeSquared]

/-- Every antiperiodic circle mode lifts a sphere zero mode to positive energy. -/
theorem antiperiodic_circle_lifts_sphere_zero_mode
    (scale : ℝ)
    (mode : ℤ)
    (hScale : scale ≠ 0) :
    0 < productModeSquared 0
      (scaledCircleMomentum scale
        CircleSpinStructure.antiperiodic mode) := by
  exact nonzero_circle_momentum_lifts_zero_mode 0 _
    (antiperiodic_scaled_momentum_nonzero scale mode hScale)

/--
The robust conclusion is qualitative: a primitive monopole creates a chiral
sphere kernel, but the product throat has zero modes only for a circle spin
structure admitting zero momentum. Computing the full spectrum, eta invariant
and determinant remains a separate analytic theorem.
-/
structure TwistedDiracAnalyticStatus where
  throatSpinorBundleConstructed : Prop
  monopoleTwistConstructed : Prop
  productDiracOperatorDefined : Prop
  indexTheoremApplied : Prop
  circleSpinStructureSelected : Prop
  fullSpectrumComputed : Prop
  etaInvariantRegularized : Prop
  determinantDefined : Prop
  effectiveActionDerived : Prop


def twistedDiracAnalyticClosure
    (s : TwistedDiracAnalyticStatus) : Prop :=
  s.throatSpinorBundleConstructed /\
  s.monopoleTwistConstructed /\
  s.productDiracOperatorDefined /\
  s.indexTheoremApplied /\
  s.circleSpinStructureSelected /\
  s.fullSpectrumComputed /\
  s.etaInvariantRegularized /\
  s.determinantDefined /\
  s.effectiveActionDerived

end P0EFTJanusTwistedDiracZeroModes
end JanusFormal

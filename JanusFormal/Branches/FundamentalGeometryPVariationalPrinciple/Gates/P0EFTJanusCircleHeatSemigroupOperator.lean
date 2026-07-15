import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleDiracHeatFunctionalBridge

/-!
# Bounded circle heat-semigroup operator

This gate packages the spectral Gaussian multipliers attached to the closed
self-adjoint circle Fourier--Dirac operator into genuine bounded continuous
linear operators on `ℓ²(ℤ, ℂ)`.  The operator is a contraction, acts on each
Fourier vector by the expected heat weight, is the identity at time zero, and
satisfies the semigroup law for nonnegative times.  Its diagonal coefficients
and their explicit sums agree with the previously proved spectral heat weights
and traces.

The construction is the concrete diagonal Fourier multiplier.  It is not
identified here with an abstract functional-calculus exponential of `D²`, and
no abstract trace-class claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatSemigroupOperator

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleDiracHeatFunctionalBridge
open scoped BigOperators ComplexConjugate ENNReal lp

/-- The heat semigroup includes time zero, unlike the strictly positive trace
regulator `HeatTime`. -/
abbrev HeatSemigroupTime := {time : ℝ // 0 ≤ time}

/-- Zero semigroup time. -/
def zeroHeatSemigroupTime : HeatSemigroupTime := ⟨0, le_rfl⟩

/-- Addition of nonnegative semigroup times. -/
def addHeatSemigroupTime
    (first second : HeatSemigroupTime) : HeatSemigroupTime :=
  ⟨first.1 + second.1, add_nonneg first.2 second.2⟩

/-- A strictly positive regulator time regarded as a semigroup time. -/
def heatTimeToSemigroupTime (time : HeatTime) : HeatSemigroupTime :=
  ⟨time.1, le_of_lt time.2⟩

/-- Gaussian multiplier derived from the squared diagonal coefficient of the
actual twice-applied unbounded Dirac operator. -/
def circleHeatMultiplier
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) : ℂ :=
  (Real.exp
    (-time.1 * circleOperatorSquaredEigenvalue fold twist mode) : ℂ)

theorem circleHeatMultiplier_norm_le_one
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) :
    ‖circleHeatMultiplier time fold twist mode‖ ≤ 1 := by
  have hSquared :
      0 ≤ circleOperatorSquaredEigenvalue fold twist mode := by
    rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
    exact eigenvalueSq_nonnegative fold twist mode
  have hExponent :
      -time.1 * circleOperatorSquaredEigenvalue fold twist mode ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.2) hSquared
  rw [circleHeatMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_one_iff.mpr hExponent)

/-- Coordinatewise Gaussian multiplication as a linear map on the circle
Hilbert space. -/
def circleHeatLinearMap
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →ₗ[ℂ] CircleHilbert where
  toFun state := ⟨fun mode => circleHeatMultiplier time fold twist mode * state mode, by
    refine state.2.mono' ?_
    intro mode
    simpa using mul_le_mul_of_nonneg_right
      (circleHeatMultiplier_norm_le_one time fold twist mode)
      (norm_nonneg (state mode))⟩
  map_add' := by
    intro first second
    ext mode
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext mode
    simp [mul_left_comm]

/-- The genuine bounded heat operator on `ℓ²(ℤ, ℂ)`. -/
noncomputable def circleHeatSemigroup
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (circleHeatLinearMap time fold twist).mkContinuous 1 (by
    intro state
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
    intro mode
    change ‖circleHeatMultiplier time fold twist mode * state mode‖ ≤
      ‖state mode‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg (state mode))
      (circleHeatMultiplier_norm_le_one time fold twist mode))

@[simp]
theorem circleHeatSemigroup_apply
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleHeatSemigroup time fold twist state mode =
      circleHeatMultiplier time fold twist mode * state mode :=
  rfl

/-- Every heat operator is a contraction. -/
theorem circleHeatSemigroup_norm_apply_le
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) :
    ‖circleHeatSemigroup time fold twist state‖ ≤ ‖state‖ := by
  apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
  intro mode
  rw [circleHeatSemigroup_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg (state mode))
    (circleHeatMultiplier_norm_le_one time fold twist mode)

/-- Operator-norm control for the heat contraction. -/
theorem circleHeatSemigroup_opNorm_le_one
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist) :
    ‖circleHeatSemigroup time fold twist‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Exact diagonal action on each Fourier basis vector. -/
theorem circleHeatSemigroup_on_basis
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) :
    circleHeatSemigroup time fold twist (circleFourierBasis mode) =
      circleHeatMultiplier time fold twist mode • circleFourierBasis mode := by
  ext other
  rw [circleHeatSemigroup_apply]
  by_cases hOther : other = mode
  · subst other
    simp [circleFourierBasis_eq_single]
  · simp [circleFourierBasis_eq_single, lp.single_apply, hOther]

/-- At zero time every diagonal multiplier is one. -/
@[simp]
theorem circleHeatMultiplier_zero
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleHeatMultiplier zeroHeatSemigroupTime fold twist mode = 1 := by
  change (Real.exp
    (-0 * circleOperatorSquaredEigenvalue fold twist mode) : ℂ) = 1
  norm_num

/-- The bounded heat semigroup starts at the identity operator. -/
theorem circleHeatSemigroup_zero
    (fold : Fold) (twist : CircleTwist) :
    circleHeatSemigroup zeroHeatSemigroupTime fold twist =
      ContinuousLinearMap.id ℂ CircleHilbert := by
  ext state mode
  simp [circleHeatSemigroup_apply]

/-- Modewise multiplicativity of the heat multipliers. -/
theorem circleHeatMultiplier_add
    (first second : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) :
    circleHeatMultiplier (addHeatSemigroupTime first second) fold twist mode =
      circleHeatMultiplier first fold twist mode *
        circleHeatMultiplier second fold twist mode := by
  rw [circleHeatMultiplier, circleHeatMultiplier, circleHeatMultiplier]
  change (Real.exp
      (-(first.1 + second.1) *
        circleOperatorSquaredEigenvalue fold twist mode) : ℂ) = _
  rw [show -(first.1 + second.1) *
      circleOperatorSquaredEigenvalue fold twist mode =
        -first.1 * circleOperatorSquaredEigenvalue fold twist mode +
          -second.1 * circleOperatorSquaredEigenvalue fold twist mode by ring,
    Real.exp_add]
  norm_num

/-- Semigroup composition law as an equality of continuous linear maps. -/
theorem circleHeatSemigroup_add
    (first second : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatSemigroup (addHeatSemigroupTime first second) fold twist =
      (circleHeatSemigroup first fold twist).comp
        (circleHeatSemigroup second fold twist) := by
  ext state mode
  rw [circleHeatSemigroup_apply, ContinuousLinearMap.comp_apply,
    circleHeatSemigroup_apply, circleHeatSemigroup_apply,
    circleHeatMultiplier_add]
  ring

/-- At positive regulator time, the bounded operator multiplier is precisely
the previously defined operator-derived heat weight. -/
theorem circleHeatMultiplier_of_heatTime_eq_operatorHeatWeight
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleHeatMultiplier (heatTimeToSemigroupTime time) fold twist mode =
      (circleOperatorHeatWeight time fold twist mode : ℂ) := by
  rfl

/-- The real diagonal matrix coefficient of the bounded operator. -/
def circleHeatDiagonalCoefficient
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) : ℝ :=
  Complex.re (inner ℂ (circleFourierBasis mode)
    (circleHeatSemigroup time fold twist (circleFourierBasis mode)))

theorem circleHeatDiagonalCoefficient_eq_multiplier_re
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) :
    circleHeatDiagonalCoefficient time fold twist mode =
      (circleHeatMultiplier time fold twist mode).re := by
  rw [circleHeatDiagonalCoefficient, circleHeatSemigroup_on_basis,
    circleFourierBasis_inner_left]
  simp [circleFourierBasis_eq_single]

/-- Positive-time diagonal coefficients recover the earlier heat weights. -/
theorem circleHeatDiagonalCoefficient_of_heatTime_eq_operatorHeatWeight
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleHeatDiagonalCoefficient (heatTimeToSemigroupTime time)
        fold twist mode =
      circleOperatorHeatWeight time fold twist mode := by
  rw [circleHeatDiagonalCoefficient_eq_multiplier_re,
    circleHeatMultiplier_of_heatTime_eq_operatorHeatWeight]
  simp

/-- Explicit diagonal sum of the bounded operator at positive time.  This is
only a concrete summable series, not an abstract trace-class assertion. -/
def circleHeatSemigroupDiagonalTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : ℝ :=
  ∑' mode : ℤ,
    circleHeatDiagonalCoefficient (heatTimeToSemigroupTime time)
      fold twist mode

theorem circleHeatSemigroupDiagonalTrace_eq_operatorEvenHeatTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatSemigroupDiagonalTrace time fold twist =
      circleOperatorEvenHeatTrace time fold twist := by
  unfold circleHeatSemigroupDiagonalTrace circleOperatorEvenHeatTrace
  apply tsum_congr
  intro mode
  rw [circleHeatDiagonalCoefficient_of_heatTime_eq_operatorHeatWeight,
    circleSpectralHeatMode_diagonal]

/-- The corresponding chirality-weighted diagonal series. -/
def circleHeatSemigroupChiralDiagonalTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : ℝ :=
  ∑' mode : ℤ, fold.chirality *
    circleHeatDiagonalCoefficient (heatTimeToSemigroupTime time)
      fold twist mode

theorem circleHeatSemigroupChiralDiagonalTrace_eq_operatorChiralHeatTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatSemigroupChiralDiagonalTrace time fold twist =
      circleOperatorChiralHeatTrace time fold twist := by
  unfold circleHeatSemigroupChiralDiagonalTrace circleOperatorChiralHeatTrace
  apply tsum_congr
  intro mode
  rw [circleHeatDiagonalCoefficient_of_heatTime_eq_operatorHeatWeight,
    circleSpectralHeatMode_diagonal]

/-- The bounded-operator chiral diagonal series cancels between PT folds. -/
theorem circleHeatSemigroupChiralDiagonalTrace_positive_add_pt_eq_zero
    (time : HeatTime) (twist : CircleTwist) :
    circleHeatSemigroupChiralDiagonalTrace time .positive twist +
      circleHeatSemigroupChiralDiagonalTrace time .pt twist = 0 := by
  rw [circleHeatSemigroupChiralDiagonalTrace_eq_operatorChiralHeatTrace,
    circleHeatSemigroupChiralDiagonalTrace_eq_operatorChiralHeatTrace]
  exact circleOperatorChiralHeatTrace_positive_add_pt_eq_zero time twist

end

end P0EFTJanusCircleHeatSemigroupOperator
end JanusFormal

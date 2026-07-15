import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatSemigroupStrongContinuity
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness of the positive-time circle heat semigroup

For strictly positive time, the diagonal circle heat operator is the
operator-norm limit of its finite Fourier truncations.  Each truncation is a
finite sum of rank-one operators and is therefore compact.  The true heat
operator is compact by norm-closedness of the compact operators.

This is a result for the one-dimensional diagonal circle model.  It does not
assert an abstract trace-class API statement or construct the full Janus
Dirac heat kernel.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatSemigroupCompactness

set_option autoImplicit false

noncomputable section

open Filter Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatSemigroupStrongContinuity
open scoped BigOperators ENNReal lp

/-- Symmetric finite window of integer Fourier modes. -/
def circleFourierWindow (cutoff : ℕ) : Finset ℤ :=
  Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)

/-- Finite Fourier truncation of the circle heat operator. -/
def circleHeatFiniteTruncation
    (cutoff : ℕ) (time : HeatSemigroupTime) (fold : Fold)
    (twist : CircleTwist) : CircleHilbert →L[ℂ] CircleHilbert :=
  ∑ mode ∈ circleFourierWindow cutoff,
    circleHeatMultiplier time fold twist mode •
      InnerProductSpace.rankOne ℂ
        (circleFourierBasis mode) (circleFourierBasis mode)

theorem circleFourierRankOne_apply
    (basisMode : ℤ) (state : CircleHilbert) (mode : ℤ) :
    InnerProductSpace.rankOne ℂ
        (circleFourierBasis basisMode) (circleFourierBasis basisMode)
        state mode =
      if mode = basisMode then state basisMode else 0 := by
  rw [InnerProductSpace.rankOne_apply,
    circleFourierBasis_inner_left]
  by_cases hMode : mode = basisMode
  · subst mode
    simp [circleFourierBasis_eq_single]
  · rw [if_neg hMode]
    simp [circleFourierBasis_eq_single, lp.single_apply, hMode]

theorem circleWeightedFourierRankOne_apply
    (scalar : ℂ) (basisMode : ℤ) (state : CircleHilbert) (mode : ℤ) :
    (scalar • InnerProductSpace.rankOne ℂ
        (circleFourierBasis basisMode) (circleFourierBasis basisMode))
        state mode =
      if mode = basisMode then scalar * state basisMode else 0 := by
  change scalar *
      (InnerProductSpace.rankOne ℂ
        (circleFourierBasis basisMode) (circleFourierBasis basisMode)
        state mode) = _
  rw [circleFourierRankOne_apply]
  by_cases hMode : mode = basisMode <;> simp [hMode]

/-- The truncation keeps exactly the heat-weighted coordinates in its finite
Fourier window. -/
@[simp]
theorem circleHeatFiniteTruncation_apply
    (cutoff : ℕ) (time : HeatSemigroupTime) (fold : Fold)
    (twist : CircleTwist) (state : CircleHilbert) (mode : ℤ) :
    circleHeatFiniteTruncation cutoff time fold twist state mode =
      if mode ∈ circleFourierWindow cutoff then
        circleHeatMultiplier time fold twist mode * state mode
      else 0 := by
  classical
  let summand : ℤ → CircleHilbert →L[ℂ] CircleHilbert := fun other =>
    circleHeatMultiplier time fold twist other •
      InnerProductSpace.rankOne ℂ
        (circleFourierBasis other) (circleFourierBasis other)
  change ((∑ other ∈ circleFourierWindow cutoff, summand other) state) mode = _
  have hApply :
      (∑ other ∈ circleFourierWindow cutoff, summand other) state =
        ∑ other ∈ circleFourierWindow cutoff, summand other state := by
    change (ContinuousLinearMap.apply ℂ CircleHilbert state)
        (∑ other ∈ circleFourierWindow cutoff, summand other) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro other _
    rfl
  rw [hApply]
  have hEvaluate :
      ((∑ other ∈ circleFourierWindow cutoff,
          summand other state : CircleHilbert) : CircleHilbert) mode =
        ∑ other ∈ circleFourierWindow cutoff, (summand other state) mode := by
    change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode)
        (∑ other ∈ circleFourierWindow cutoff, summand other state) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro other _
    rfl
  rw [hEvaluate]
  simp only [summand, circleWeightedFourierRankOne_apply]
  by_cases hMode : mode ∈ circleFourierWindow cutoff
  · rw [if_pos hMode, Finset.sum_eq_single mode]
    · simp
    · intro other hOther hOtherMode
      have hModeOther : mode ≠ other := Ne.symm hOtherMode
      simp [hModeOther]
    · intro hNotMode
      exact (hNotMode hMode).elim
  · rw [if_neg hMode]
    apply Finset.sum_eq_zero
    intro other hOther
    have hModeOther : mode ≠ other := by
      intro hEqual
      subst other
      exact hMode hOther
    simp [hModeOther]

/-- A rank-one Fourier projection is compact because it factors through the
one-dimensional scalar field. -/
theorem circleFourierRankOne_isCompact (mode : ℤ) :
    IsCompactOperator
      (InnerProductSpace.rankOne ℂ
        (circleFourierBasis mode) (circleFourierBasis mode)) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (innerSL ℂ (circleFourierBasis mode))).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ (circleFourierBasis mode))

/-- Every finite Fourier heat truncation is compact. -/
theorem circleHeatFiniteTruncation_isCompact
    (cutoff : ℕ) (time : HeatSemigroupTime) (fold : Fold)
    (twist : CircleTwist) :
    IsCompactOperator (circleHeatFiniteTruncation cutoff time fold twist) := by
  classical
  unfold circleHeatFiniteTruncation
  refine Finset.sum_induction
    (fun mode => circleHeatMultiplier time fold twist mode •
      InnerProductSpace.rankOne ℂ
        (circleFourierBasis mode) (circleFourierBasis mode))
    (fun operator => IsCompactOperator operator)
    (fun _ _ hFirst hSecond => hFirst.add hSecond)
    isCompactOperator_zero ?_
  intro mode _
  exact (circleFourierRankOne_isCompact mode).smul
    (circleHeatMultiplier time fold twist mode)

/-- Outside the window `[-N,N]`, the shifted squared Fourier eigenvalue is at
least `N²`. -/
theorem cutoff_square_le_eigenvalueSq_of_not_mem
    (cutoff : ℕ) (fold : Fold) (twist : CircleTwist) (mode : ℤ)
    (hMode : mode ∉ circleFourierWindow cutoff) :
    ((cutoff : ℝ) ^ 2) ≤ eigenvalueSq fold twist mode := by
  rw [circleFourierWindow, Finset.mem_Icc, not_and_or] at hMode
  unfold eigenvalueSq diracEigenvalue baseEigenvalue
  cases fold <;> simp only [Fold.positive_spectralSign,
    Fold.pt_spectralSign, one_mul, neg_one_mul]
  all_goals
    rcases hMode with hLow | hHigh
    · have hModeInt : mode ≤ -(cutoff : ℤ) - 1 := by omega
      have hModeReal : (mode : ℝ) ≤ -(cutoff : ℝ) - 1 := by
        exact_mod_cast hModeInt
      have hShift : (mode : ℝ) + twist.value ≤ -(cutoff : ℝ) := by
        linarith [twist.le_one]
      nlinarith [sq_nonneg ((mode : ℝ) + twist.value + (cutoff : ℝ))]
    · have hModeInt : (cutoff : ℤ) + 1 ≤ mode := by omega
      have hModeReal : (cutoff : ℝ) + 1 ≤ (mode : ℝ) := by
        exact_mod_cast hModeInt
      have hShift : (cutoff : ℝ) ≤ (mode : ℝ) + twist.value := by
        linarith [twist.nonnegative]
      nlinarith [sq_nonneg ((mode : ℝ) + twist.value - (cutoff : ℝ))]

/-- Gaussian operator-norm tail bound. -/
def circleHeatTailBound (time : HeatTime) (cutoff : ℕ) : ℝ :=
  Real.exp (-time.1 * (cutoff : ℝ) ^ 2)

theorem circleHeatTailBound_pos (time : HeatTime) (cutoff : ℕ) :
    0 < circleHeatTailBound time cutoff :=
  Real.exp_pos _

theorem circleHeatMultiplier_norm_le_tailBound_of_not_mem
    (time : HeatTime) (cutoff : ℕ) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) (hMode : mode ∉ circleFourierWindow cutoff) :
    ‖circleHeatMultiplier (heatTimeToSemigroupTime time) fold twist mode‖ ≤
      circleHeatTailBound time cutoff := by
  rw [circleHeatMultiplier, circleHeatTailBound, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hSpectrum := cutoff_square_le_eigenvalueSq_of_not_mem
    cutoff fold twist mode hMode
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  change -time.1 * eigenvalueSq fold twist mode ≤
    -time.1 * (cutoff : ℝ) ^ 2
  nlinarith [time.2]

/-- At positive time, the absolute values of the diagonal heat multipliers
form a summable series.  This is an explicit series statement, not an
abstract trace-class assertion. -/
theorem circleHeatMultiplier_norm_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : ℤ =>
      ‖circleHeatMultiplier
        (heatTimeToSemigroupTime time) fold twist mode‖) := by
  refine (circleOperatorHeatWeight_summable time fold twist).congr
    (fun mode => ?_)
  rw [circleHeatMultiplier_of_heatTime_eq_operatorHeatWeight,
    Complex.norm_real, Real.norm_eq_abs]
  exact (abs_of_pos (by
    unfold circleOperatorHeatWeight
    exact Real.exp_pos _)).symm

/-- The error on every vector is controlled by the same Gaussian tail. -/
theorem circleHeatSemigroup_sub_truncation_norm_apply_le
    (time : HeatTime) (cutoff : ℕ) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) :
    ‖(circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist -
        circleHeatFiniteTruncation cutoff
          (heatTimeToSemigroupTime time) fold twist) state‖ ≤
      circleHeatTailBound time cutoff * ‖state‖ := by
  let tail : ℂ := (circleHeatTailBound time cutoff : ℂ)
  calc
    _ ≤ ‖tail • state‖ := by
      apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
      intro mode
      change
        ‖circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist state mode -
          circleHeatFiniteTruncation cutoff
            (heatTimeToSemigroupTime time) fold twist state mode‖ ≤
          ‖tail * state mode‖
      by_cases hMode : mode ∈ circleFourierWindow cutoff
      · rw [circleHeatSemigroup_apply,
          circleHeatFiniteTruncation_apply, if_pos hMode, sub_self,
          norm_zero]
        positivity
      · rw [circleHeatSemigroup_apply, circleHeatFiniteTruncation_apply,
          if_neg hMode, sub_zero, norm_mul]
        rw [norm_mul]
        have hTailNorm : ‖tail‖ = circleHeatTailBound time cutoff := by
          change ‖(circleHeatTailBound time cutoff : ℂ)‖ = _
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (circleHeatTailBound_pos time cutoff)]
        rw [hTailNorm]
        exact mul_le_mul_of_nonneg_right
          (circleHeatMultiplier_norm_le_tailBound_of_not_mem
            time cutoff fold twist mode hMode)
          (norm_nonneg (state mode))
    _ = circleHeatTailBound time cutoff * ‖state‖ := by
      rw [norm_smul]
      change ‖(circleHeatTailBound time cutoff : ℂ)‖ * ‖state‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (circleHeatTailBound_pos time cutoff)]

/-- Explicit operator-norm approximation estimate. -/
theorem circleHeatSemigroup_sub_truncation_opNorm_le
    (time : HeatTime) (cutoff : ℕ) (fold : Fold) (twist : CircleTwist) :
    ‖circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist -
        circleHeatFiniteTruncation cutoff
          (heatTimeToSemigroupTime time) fold twist‖ ≤
      circleHeatTailBound time cutoff := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (Real.exp_pos _))
  exact circleHeatSemigroup_sub_truncation_norm_apply_le
    time cutoff fold twist

/-- The explicit Gaussian tail tends to zero. -/
theorem circleHeatTailBound_tendsto_zero (time : HeatTime) :
    Tendsto (circleHeatTailBound time) atTop (nhds 0) := by
  unfold circleHeatTailBound
  apply Real.tendsto_exp_atBot.comp
  have hSquare : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) ^ 2)
      atTop atTop := by
    have hCast : Tendsto (fun cutoff : ℕ => (cutoff : ℝ))
        atTop atTop := tendsto_natCast_atTop_atTop
    simpa [pow_two] using hCast.atTop_mul_atTop₀ hCast
  exact hSquare.const_mul_atTop_of_neg (neg_lt_zero.mpr time.2)

/-- Finite Fourier truncations converge to the true heat operator in operator
norm for every strictly positive time. -/
theorem circleHeatFiniteTruncation_tendsto_heatSemigroup
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Tendsto
      (fun cutoff : ℕ => circleHeatFiniteTruncation cutoff
        (heatTimeToSemigroupTime time) fold twist)
      atTop
      (nhds (circleHeatSemigroup
        (heatTimeToSemigroupTime time) fold twist)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hNorm : Tendsto
      (fun cutoff : ℕ =>
        ‖circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist -
          circleHeatFiniteTruncation cutoff
            (heatTimeToSemigroupTime time) fold twist‖)
      atTop (nhds 0) := by
    exact squeeze_zero (fun _ => norm_nonneg _)
      (circleHeatSemigroup_sub_truncation_opNorm_le time · fold twist)
      (circleHeatTailBound_tendsto_zero time)
  simpa [norm_sub_rev] using hNorm

/-- At every strictly positive time, the genuine circle heat semigroup is a
compact operator on the full Fourier Hilbert space. -/
theorem circleHeatSemigroup_isCompact
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    IsCompactOperator
      (circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist) := by
  apply isCompactOperator_of_tendsto
    (circleHeatFiniteTruncation_tendsto_heatSemigroup time fold twist)
  exact Filter.Eventually.of_forall (fun cutoff =>
    circleHeatFiniteTruncation_isCompact cutoff
      (heatTimeToSemigroupTime time) fold twist)

end

end P0EFTJanusCircleHeatSemigroupCompactness
end JanusFormal

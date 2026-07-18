import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceDerivative

/-!
# Positive-time second derivative of the circle nuclear heat trace

Two spectral factors are absorbed by successively halving the positive lower
time.  This gives a summable majorant, justifies a second termwise derivative,
and proves its positivity and PT covariance.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatNuclearTraceSecondDerivative

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceDerivative

def circleHeatWeightRealSecondDerivative
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) : Real :=
  circleOperatorSquaredEigenvalue fold twist mode ^ 2 *
    circleHeatWeightReal time fold twist mode

def circleHeatNuclearTraceRealSecondDerivative
    (time : Real) (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' mode : Int, circleHeatWeightRealSecondDerivative time fold twist mode

theorem circleHeatWeightRealDerivative_hasDerivAt
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) :
    HasDerivAt
      (fun s : Real => circleHeatWeightRealDerivative s fold twist mode)
      (circleHeatWeightRealSecondDerivative time fold twist mode) time := by
  have h := (circleHeatWeightReal_hasDerivAt time fold twist mode).const_mul
    (-circleOperatorSquaredEigenvalue fold twist mode)
  simpa [circleHeatWeightRealDerivative,
    circleHeatWeightRealSecondDerivative, pow_two, mul_assoc] using h

theorem circleHeatWeightRealSecondDerivative_continuous
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    Continuous (fun time : Real =>
      circleHeatWeightRealSecondDerivative time fold twist mode) := by
  unfold circleHeatWeightRealSecondDerivative
  exact continuous_const.mul (circleHeatWeightReal_continuous fold twist mode)

theorem spectralFactor_sq_mul_exp_bound
    {epsilon spectrum : Real} (hEpsilon : 0 < epsilon)
    (hSpectrum : 0 ≤ spectrum) :
    spectrum ^ 2 * Real.exp (-epsilon * spectrum) ≤
      ((2 / epsilon * Real.exp (-1)) *
        (2 / (epsilon / 2) * Real.exp (-1))) *
          Real.exp (-(epsilon / 4) * spectrum) := by
  have hFirst := spectralFactor_mul_exp_bound
    (epsilon := epsilon) (spectrum := spectrum) hEpsilon
  have hSecond := spectralFactor_mul_exp_bound
    (epsilon := epsilon / 2) (spectrum := spectrum) (half_pos hEpsilon)
  have hConstant : 0 ≤ 2 / epsilon * Real.exp (-1) :=
    mul_nonneg (div_nonneg (by norm_num) hEpsilon.le) (Real.exp_pos _).le
  calc
    spectrum ^ 2 * Real.exp (-epsilon * spectrum) =
        spectrum * (spectrum * Real.exp (-epsilon * spectrum)) := by ring
    _ ≤ spectrum * ((2 / epsilon * Real.exp (-1)) *
          Real.exp (-(epsilon / 2) * spectrum)) :=
      mul_le_mul_of_nonneg_left hFirst hSpectrum
    _ = (2 / epsilon * Real.exp (-1)) *
          (spectrum * Real.exp (-(epsilon / 2) * spectrum)) := by ring
    _ ≤ (2 / epsilon * Real.exp (-1)) *
          ((2 / (epsilon / 2) * Real.exp (-1)) *
            Real.exp (-((epsilon / 2) / 2) * spectrum)) :=
      mul_le_mul_of_nonneg_left hSecond hConstant
    _ = ((2 / epsilon * Real.exp (-1)) *
          (2 / (epsilon / 2) * Real.exp (-1))) *
            Real.exp (-(epsilon / 4) * spectrum) := by ring_nf

theorem circleHeatWeightRealSecondDerivative_uniform_summable
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : Int =>
      ((2 / epsilon.1 * Real.exp (-1)) *
        (2 / (epsilon.1 / 2) * Real.exp (-1))) *
          circleHeatWeightReal (epsilon.1 / 4) fold twist mode) := by
  exact Summable.mul_left _ (circleHeatWeightReal_uniform_summable
    ⟨epsilon.1 / 4, div_pos epsilon.2 (by norm_num)⟩ fold twist)

theorem circleHeatWeightRealSecondDerivative_norm_le
    (epsilon : HeatTime) {time : Real} (hTime : epsilon.1 ≤ time)
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    ‖circleHeatWeightRealSecondDerivative time fold twist mode‖ ≤
      ((2 / epsilon.1 * Real.exp (-1)) *
        (2 / (epsilon.1 / 2) * Real.exp (-1))) *
          circleHeatWeightReal (epsilon.1 / 4) fold twist mode := by
  have hSpectrum := circleOperatorSquaredEigenvalue_nonnegative fold twist mode
  rw [circleHeatWeightRealSecondDerivative, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (by unfold circleHeatWeightReal; exact (Real.exp_pos _).le))]
  refine (mul_le_mul_of_nonneg_left
    (circleHeatWeightReal_le_of_le hTime fold twist mode)
    (sq_nonneg _)).trans ?_
  unfold circleHeatWeightReal
  exact spectralFactor_sq_mul_exp_bound epsilon.2 hSpectrum

theorem circleHeatNuclearTraceRealSecondDerivative_continuousOn_Ici
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceRealSecondDerivative time fold twist)
      (Ici epsilon.1) := by
  unfold circleHeatNuclearTraceRealSecondDerivative
  apply continuousOn_tsum
  · intro mode
    exact (circleHeatWeightRealSecondDerivative_continuous
      fold twist mode).continuousOn
  · exact circleHeatWeightRealSecondDerivative_uniform_summable
      epsilon fold twist
  · intro mode time hTime
    exact circleHeatWeightRealSecondDerivative_norm_le
      epsilon hTime fold twist mode

theorem circleHeatNuclearTraceRealSecondDerivative_continuousOn_Ioi
    (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceRealSecondDerivative time fold twist) (Ioi 0) := by
  intro time hTime
  let epsilon : HeatTime := ⟨time / 2, half_pos hTime⟩
  have hLocal := circleHeatNuclearTraceRealSecondDerivative_continuousOn_Ici
    epsilon fold twist
  exact (hLocal.continuousAt
    (Ici_mem_nhds (half_lt_self hTime))).continuousWithinAt

theorem circleHeatNuclearTraceRealDerivative_hasDerivAt
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    HasDerivAt
      (fun s : Real => circleHeatNuclearTraceRealDerivative s fold twist)
      (circleHeatNuclearTraceRealSecondDerivative time.1 fold twist)
      time.1 := by
  unfold circleHeatNuclearTraceRealDerivative
    circleHeatNuclearTraceRealSecondDerivative
  let epsilon : HeatTime := ⟨time.1 / 2, half_pos time.2⟩
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun mode s => circleHeatWeightRealDerivative s fold twist mode)
    (g' := fun mode s => circleHeatWeightRealSecondDerivative s fold twist mode)
    (u := fun mode : Int =>
      ((2 / epsilon.1 * Real.exp (-1)) *
        (2 / (epsilon.1 / 2) * Real.exp (-1))) *
          circleHeatWeightReal (epsilon.1 / 4) fold twist mode)
    (t := Ioi epsilon.1) (y₀ := time.1) (y := time.1)
  · exact circleHeatWeightRealSecondDerivative_uniform_summable
      epsilon fold twist
  · exact isOpen_Ioi
  · exact isPreconnected_Ioi
  · intro mode s _
    exact circleHeatWeightRealDerivative_hasDerivAt s fold twist mode
  · intro mode s hs
    exact circleHeatWeightRealSecondDerivative_norm_le
      epsilon hs.le fold twist mode
  · exact mem_Ioi.mpr (half_lt_self time.2)
  · exact circleHeatWeightRealDerivative_summable time fold twist
  · exact mem_Ioi.mpr (half_lt_self time.2)

theorem circleHeatNuclearTraceRealDerivative_deriv_eq
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    deriv (fun s : Real =>
      circleHeatNuclearTraceRealDerivative s fold twist) time.1 =
        circleHeatNuclearTraceRealSecondDerivative time.1 fold twist :=
  (circleHeatNuclearTraceRealDerivative_hasDerivAt time fold twist).deriv

theorem circleHeatNuclearTraceRealSecondDerivative_nonnegative
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    0 ≤ circleHeatNuclearTraceRealSecondDerivative time.1 fold twist := by
  unfold circleHeatNuclearTraceRealSecondDerivative
  apply tsum_nonneg
  intro mode
  exact mul_nonneg (sq_nonneg _)
    (by unfold circleHeatWeightReal; exact (Real.exp_pos _).le)

theorem circleHeatNuclearTraceRealDerivative_deriv_nonnegative
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    0 ≤ deriv (fun s : Real =>
      circleHeatNuclearTraceRealDerivative s fold twist) time.1 := by
  rw [circleHeatNuclearTraceRealDerivative_deriv_eq time fold twist]
  exact circleHeatNuclearTraceRealSecondDerivative_nonnegative time fold twist

theorem circleHeatNuclearTraceRealDerivative_contDiffOn_one
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ 1
      (fun time : Real => circleHeatNuclearTraceRealDerivative time fold twist)
      (Ioi 0) := by
  change ContDiffOn ℝ (0 + 1)
    (fun time : Real => circleHeatNuclearTraceRealDerivative time fold twist)
    (Ioi 0)
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · intro time hTime
    exact (circleHeatNuclearTraceRealDerivative_hasDerivAt
      ⟨time, hTime⟩ fold twist).differentiableAt.differentiableWithinAt
  · intro hImpossible
    norm_num at hImpossible
  · rw [contDiffOn_zero]
    exact (circleHeatNuclearTraceRealSecondDerivative_continuousOn_Ioi
      fold twist).congr fun time hTime =>
        (circleHeatNuclearTraceRealDerivative_deriv_eq
          ⟨time, hTime⟩ fold twist)

theorem circleHeatNuclearTraceReal_contDiffOn_two
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ 2
      (fun time : Real => circleHeatNuclearTraceReal time fold twist)
      (Ioi 0) := by
  change ContDiffOn ℝ (1 + 1)
    (fun time : Real => circleHeatNuclearTraceReal time fold twist) (Ioi 0)
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · intro time hTime
    exact (circleHeatNuclearTraceReal_hasDerivAt
      ⟨time, hTime⟩ fold twist).differentiableAt.differentiableWithinAt
  · intro hImpossible
    norm_num at hImpossible
  · exact (circleHeatNuclearTraceRealDerivative_contDiffOn_one
      fold twist).congr fun time hTime =>
        (circleHeatNuclearTraceReal_deriv_eq
          ⟨time, hTime⟩ fold twist)

theorem circleHeatNuclearTraceRealSecondDerivative_pt_eq_positive
    (time : Real) (twist : CircleTwist) :
    circleHeatNuclearTraceRealSecondDerivative time .pt twist =
      circleHeatNuclearTraceRealSecondDerivative time .positive twist := by
  unfold circleHeatNuclearTraceRealSecondDerivative
  apply tsum_congr
  intro mode
  unfold circleHeatWeightRealSecondDerivative
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    pt_eigenvalueSq_eq_positive,
    circleHeatWeightReal_pt_eq_positive]

end
end P0EFTJanusCircleHeatNuclearTraceSecondDerivative
end JanusFormal

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceSecondDerivative

/-!
# Positive-time third derivative of the circle nuclear heat trace

A third spectral factor is absorbed by one further Gaussian half-time.  The
third termwise derivative is therefore legitimate, continuous, nonpositive,
PT invariant, and certifies `C³` regularity for positive time.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatNuclearTraceThirdDerivative

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceDerivative
open P0EFTJanusCircleHeatNuclearTraceSecondDerivative

def circleHeatWeightRealThirdDerivative
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) : Real :=
  -(circleOperatorSquaredEigenvalue fold twist mode ^ 3) *
    circleHeatWeightReal time fold twist mode

def circleHeatNuclearTraceRealThirdDerivative
    (time : Real) (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' mode : Int, circleHeatWeightRealThirdDerivative time fold twist mode

theorem circleHeatWeightRealSecondDerivative_hasDerivAt
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) :
    HasDerivAt
      (fun s : Real => circleHeatWeightRealSecondDerivative s fold twist mode)
      (circleHeatWeightRealThirdDerivative time fold twist mode) time := by
  have h := (circleHeatWeightReal_hasDerivAt time fold twist mode).const_mul
    (circleOperatorSquaredEigenvalue fold twist mode ^ 2)
  simpa [circleHeatWeightRealSecondDerivative,
    circleHeatWeightRealThirdDerivative, circleHeatWeightRealDerivative,
    pow_succ, mul_assoc] using h

theorem circleHeatWeightRealThirdDerivative_continuous
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    Continuous (fun time : Real =>
      circleHeatWeightRealThirdDerivative time fold twist mode) := by
  unfold circleHeatWeightRealThirdDerivative
  exact continuous_const.mul (circleHeatWeightReal_continuous fold twist mode)

theorem spectralFactor_cube_mul_exp_bound
    {epsilon spectrum : Real} (hEpsilon : 0 < epsilon)
    (hSpectrum : 0 ≤ spectrum) :
    spectrum ^ 3 * Real.exp (-epsilon * spectrum) ≤
      (((2 / epsilon * Real.exp (-1)) *
          (2 / (epsilon / 2) * Real.exp (-1))) *
        (2 / (epsilon / 4) * Real.exp (-1))) *
          Real.exp (-(epsilon / 8) * spectrum) := by
  have hSecond := spectralFactor_sq_mul_exp_bound hEpsilon hSpectrum
  have hThird := spectralFactor_mul_exp_bound
    (epsilon := epsilon / 4) (spectrum := spectrum)
    (div_pos hEpsilon (by norm_num))
  have hSecondConstant :
      0 ≤ (2 / epsilon * Real.exp (-1)) *
        (2 / (epsilon / 2) * Real.exp (-1)) := by
    positivity
  calc
    spectrum ^ 3 * Real.exp (-epsilon * spectrum) =
        spectrum * (spectrum ^ 2 * Real.exp (-epsilon * spectrum)) := by ring
    _ ≤ spectrum * (((2 / epsilon * Real.exp (-1)) *
          (2 / (epsilon / 2) * Real.exp (-1))) *
            Real.exp (-(epsilon / 4) * spectrum)) :=
      mul_le_mul_of_nonneg_left hSecond hSpectrum
    _ = ((2 / epsilon * Real.exp (-1)) *
          (2 / (epsilon / 2) * Real.exp (-1))) *
            (spectrum * Real.exp (-(epsilon / 4) * spectrum)) := by ring
    _ ≤ ((2 / epsilon * Real.exp (-1)) *
          (2 / (epsilon / 2) * Real.exp (-1))) *
            ((2 / (epsilon / 4) * Real.exp (-1)) *
              Real.exp (-((epsilon / 4) / 2) * spectrum)) :=
      mul_le_mul_of_nonneg_left hThird hSecondConstant
    _ = (((2 / epsilon * Real.exp (-1)) *
          (2 / (epsilon / 2) * Real.exp (-1))) *
        (2 / (epsilon / 4) * Real.exp (-1))) *
          Real.exp (-(epsilon / 8) * spectrum) := by ring_nf

theorem circleHeatWeightRealThirdDerivative_uniform_summable
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : Int =>
      (((2 / epsilon.1 * Real.exp (-1)) *
          (2 / (epsilon.1 / 2) * Real.exp (-1))) *
        (2 / (epsilon.1 / 4) * Real.exp (-1))) *
          circleHeatWeightReal (epsilon.1 / 8) fold twist mode) := by
  exact Summable.mul_left _ (circleHeatWeightReal_uniform_summable
    ⟨epsilon.1 / 8, div_pos epsilon.2 (by norm_num)⟩ fold twist)

theorem circleHeatWeightRealThirdDerivative_norm_le
    (epsilon : HeatTime) {time : Real} (hTime : epsilon.1 ≤ time)
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    ‖circleHeatWeightRealThirdDerivative time fold twist mode‖ ≤
      (((2 / epsilon.1 * Real.exp (-1)) *
          (2 / (epsilon.1 / 2) * Real.exp (-1))) *
        (2 / (epsilon.1 / 4) * Real.exp (-1))) *
          circleHeatWeightReal (epsilon.1 / 8) fold twist mode := by
  have hSpectrum := circleOperatorSquaredEigenvalue_nonnegative fold twist mode
  rw [circleHeatWeightRealThirdDerivative, Real.norm_eq_abs,
    abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (pow_nonneg hSpectrum 3))
      (by unfold circleHeatWeightReal; exact (Real.exp_pos _).le)),
    neg_mul, neg_neg]
  refine (mul_le_mul_of_nonneg_left
    (circleHeatWeightReal_le_of_le hTime fold twist mode)
    (pow_nonneg hSpectrum 3)).trans ?_
  unfold circleHeatWeightReal
  exact spectralFactor_cube_mul_exp_bound epsilon.2 hSpectrum

theorem circleHeatNuclearTraceRealThirdDerivative_continuousOn_Ici
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceRealThirdDerivative time fold twist)
      (Ici epsilon.1) := by
  unfold circleHeatNuclearTraceRealThirdDerivative
  apply continuousOn_tsum
  · intro mode
    exact (circleHeatWeightRealThirdDerivative_continuous
      fold twist mode).continuousOn
  · exact circleHeatWeightRealThirdDerivative_uniform_summable
      epsilon fold twist
  · intro mode time hTime
    exact circleHeatWeightRealThirdDerivative_norm_le
      epsilon hTime fold twist mode

theorem circleHeatNuclearTraceRealThirdDerivative_continuousOn_Ioi
    (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceRealThirdDerivative time fold twist) (Ioi 0) := by
  intro time hTime
  let epsilon : HeatTime := ⟨time / 2, half_pos hTime⟩
  have hLocal := circleHeatNuclearTraceRealThirdDerivative_continuousOn_Ici
    epsilon fold twist
  exact (hLocal.continuousAt
    (Ici_mem_nhds (half_lt_self hTime))).continuousWithinAt

theorem circleHeatNuclearTraceRealSecondDerivative_hasDerivAt
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    HasDerivAt
      (fun s : Real => circleHeatNuclearTraceRealSecondDerivative s fold twist)
      (circleHeatNuclearTraceRealThirdDerivative time.1 fold twist)
      time.1 := by
  unfold circleHeatNuclearTraceRealSecondDerivative
    circleHeatNuclearTraceRealThirdDerivative
  let epsilon : HeatTime := ⟨time.1 / 2, half_pos time.2⟩
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun mode s => circleHeatWeightRealSecondDerivative s fold twist mode)
    (g' := fun mode s => circleHeatWeightRealThirdDerivative s fold twist mode)
    (u := fun mode : Int =>
      (((2 / epsilon.1 * Real.exp (-1)) *
          (2 / (epsilon.1 / 2) * Real.exp (-1))) *
        (2 / (epsilon.1 / 4) * Real.exp (-1))) *
          circleHeatWeightReal (epsilon.1 / 8) fold twist mode)
    (t := Ioi epsilon.1) (y₀ := time.1) (y := time.1)
  · exact circleHeatWeightRealThirdDerivative_uniform_summable
      epsilon fold twist
  · exact isOpen_Ioi
  · exact isPreconnected_Ioi
  · intro mode s _
    exact circleHeatWeightRealSecondDerivative_hasDerivAt s fold twist mode
  · intro mode s hs
    exact circleHeatWeightRealThirdDerivative_norm_le
      epsilon hs.le fold twist mode
  · exact mem_Ioi.mpr (half_lt_self time.2)
  · apply Summable.of_norm_bounded
      (circleHeatWeightRealSecondDerivative_uniform_summable time fold twist)
    intro mode
    exact circleHeatWeightRealSecondDerivative_norm_le
      time le_rfl fold twist mode
  · exact mem_Ioi.mpr (half_lt_self time.2)

theorem circleHeatNuclearTraceRealSecondDerivative_deriv_eq
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    deriv (fun s : Real =>
      circleHeatNuclearTraceRealSecondDerivative s fold twist) time.1 =
        circleHeatNuclearTraceRealThirdDerivative time.1 fold twist :=
  (circleHeatNuclearTraceRealSecondDerivative_hasDerivAt time fold twist).deriv

theorem circleHeatNuclearTraceRealThirdDerivative_nonpositive
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTraceRealThirdDerivative time.1 fold twist ≤ 0 := by
  unfold circleHeatNuclearTraceRealThirdDerivative
  apply tsum_nonpos
  intro mode
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (pow_nonneg
      (circleOperatorSquaredEigenvalue_nonnegative fold twist mode) 3))
    (by unfold circleHeatWeightReal; exact (Real.exp_pos _).le)

theorem circleHeatNuclearTraceRealSecondDerivative_contDiffOn_one
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ 1
      (fun time : Real => circleHeatNuclearTraceRealSecondDerivative time fold twist)
      (Ioi 0) := by
  change ContDiffOn ℝ (0 + 1)
    (fun time : Real => circleHeatNuclearTraceRealSecondDerivative time fold twist)
    (Ioi 0)
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · intro time hTime
    exact (circleHeatNuclearTraceRealSecondDerivative_hasDerivAt
      ⟨time, hTime⟩ fold twist).differentiableAt.differentiableWithinAt
  · intro hImpossible
    norm_num at hImpossible
  · rw [contDiffOn_zero]
    exact (circleHeatNuclearTraceRealThirdDerivative_continuousOn_Ioi
      fold twist).congr fun time hTime =>
        circleHeatNuclearTraceRealSecondDerivative_deriv_eq
          ⟨time, hTime⟩ fold twist

theorem circleHeatNuclearTraceRealDerivative_contDiffOn_two
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ 2
      (fun time : Real => circleHeatNuclearTraceRealDerivative time fold twist)
      (Ioi 0) := by
  change ContDiffOn ℝ (1 + 1)
    (fun time : Real => circleHeatNuclearTraceRealDerivative time fold twist)
    (Ioi 0)
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · intro time hTime
    exact (circleHeatNuclearTraceRealDerivative_hasDerivAt
      ⟨time, hTime⟩ fold twist).differentiableAt.differentiableWithinAt
  · intro hImpossible
    norm_num at hImpossible
  · exact (circleHeatNuclearTraceRealSecondDerivative_contDiffOn_one
      fold twist).congr fun time hTime =>
        circleHeatNuclearTraceRealDerivative_deriv_eq
          ⟨time, hTime⟩ fold twist

theorem circleHeatNuclearTraceReal_contDiffOn_three
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ 3
      (fun time : Real => circleHeatNuclearTraceReal time fold twist)
      (Ioi 0) := by
  change ContDiffOn ℝ (2 + 1)
    (fun time : Real => circleHeatNuclearTraceReal time fold twist) (Ioi 0)
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · intro time hTime
    exact (circleHeatNuclearTraceReal_hasDerivAt
      ⟨time, hTime⟩ fold twist).differentiableAt.differentiableWithinAt
  · intro hImpossible
    norm_num at hImpossible
  · exact (circleHeatNuclearTraceRealDerivative_contDiffOn_two
      fold twist).congr fun time hTime =>
        circleHeatNuclearTraceReal_deriv_eq ⟨time, hTime⟩ fold twist

theorem circleHeatNuclearTraceRealThirdDerivative_pt_eq_positive
    (time : Real) (twist : CircleTwist) :
    circleHeatNuclearTraceRealThirdDerivative time .pt twist =
      circleHeatNuclearTraceRealThirdDerivative time .positive twist := by
  unfold circleHeatNuclearTraceRealThirdDerivative
  apply tsum_congr
  intro mode
  unfold circleHeatWeightRealThirdDerivative
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    pt_eigenvalueSq_eq_positive,
    circleHeatWeightReal_pt_eq_positive]

end
end P0EFTJanusCircleHeatNuclearTraceThirdDerivative
end JanusFormal

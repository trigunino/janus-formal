import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceThirdDerivative

/-!
# Smooth positive-time circle nuclear heat trace

All spectral powers are absorbed by recursively halving a positive lower time.
The resulting summable majorants justify termwise differentiation at every
finite order and certify `C∞` regularity on the positive-time interval.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatNuclearTraceSmooth

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open Set
open scoped ContDiff
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceDerivative
open P0EFTJanusCircleHeatNuclearTraceSecondDerivative
open P0EFTJanusCircleHeatNuclearTraceThirdDerivative

def spectralAbsorptionTime : Nat → Real → Real
  | 0, epsilon => epsilon
  | order + 1, epsilon => spectralAbsorptionTime order (epsilon / 2)

def spectralAbsorptionConstant : Nat → Real → Real
  | 0, _ => 1
  | order + 1, epsilon =>
      (2 / epsilon * Real.exp (-1)) *
        spectralAbsorptionConstant order (epsilon / 2)

theorem spectralAbsorptionTime_pos
    (order : Nat) {epsilon : Real} (hEpsilon : 0 < epsilon) :
    0 < spectralAbsorptionTime order epsilon := by
  induction order generalizing epsilon with
  | zero => simpa [spectralAbsorptionTime] using hEpsilon
  | succ order ih =>
      simp only [spectralAbsorptionTime]
      exact ih (half_pos hEpsilon)

theorem spectralAbsorptionConstant_nonnegative
    (order : Nat) {epsilon : Real} (hEpsilon : 0 < epsilon) :
    0 ≤ spectralAbsorptionConstant order epsilon := by
  induction order generalizing epsilon with
  | zero => simp [spectralAbsorptionConstant]
  | succ order ih =>
      simp only [spectralAbsorptionConstant]
      exact mul_nonneg
        (mul_nonneg (div_nonneg (by norm_num) hEpsilon.le)
          (Real.exp_pos _).le)
        (ih (half_pos hEpsilon))

theorem spectralFactor_pow_mul_exp_bound
    (order : Nat) {epsilon spectrum : Real} (hEpsilon : 0 < epsilon)
    (hSpectrum : 0 ≤ spectrum) :
    spectrum ^ order * Real.exp (-epsilon * spectrum) ≤
      spectralAbsorptionConstant order epsilon *
        Real.exp (-spectralAbsorptionTime order epsilon * spectrum) := by
  induction order generalizing epsilon with
  | zero => simp [spectralAbsorptionConstant, spectralAbsorptionTime]
  | succ order ih =>
      have hFirst := spectralFactor_mul_exp_bound
        (epsilon := epsilon) (spectrum := spectrum) hEpsilon
      have hInd := ih (half_pos hEpsilon)
      have hConstant : 0 ≤ 2 / epsilon * Real.exp (-1) :=
        mul_nonneg (div_nonneg (by norm_num) hEpsilon.le)
          (Real.exp_pos _).le
      calc
        spectrum ^ (order + 1) * Real.exp (-epsilon * spectrum) =
            spectrum ^ order *
              (spectrum * Real.exp (-epsilon * spectrum)) := by
                rw [pow_succ]
                ring
        _ ≤ spectrum ^ order *
              ((2 / epsilon * Real.exp (-1)) *
                Real.exp (-(epsilon / 2) * spectrum)) :=
          mul_le_mul_of_nonneg_left hFirst (pow_nonneg hSpectrum order)
        _ = (2 / epsilon * Real.exp (-1)) *
              (spectrum ^ order *
                Real.exp (-(epsilon / 2) * spectrum)) := by ring
        _ ≤ (2 / epsilon * Real.exp (-1)) *
              (spectralAbsorptionConstant order (epsilon / 2) *
                Real.exp (-spectralAbsorptionTime order (epsilon / 2) *
                  spectrum)) :=
          mul_le_mul_of_nonneg_left hInd hConstant
        _ = spectralAbsorptionConstant (order + 1) epsilon *
              Real.exp (-spectralAbsorptionTime (order + 1) epsilon *
                spectrum) := by
          simp only [spectralAbsorptionConstant, spectralAbsorptionTime]
          ring

def circleHeatWeightRealIteratedDerivative
    (order : Nat) (time : Real) (fold : Fold) (twist : CircleTwist)
    (mode : Int) : Real :=
  (-circleOperatorSquaredEigenvalue fold twist mode) ^ order *
    circleHeatWeightReal time fold twist mode

def circleHeatNuclearTraceRealIteratedDerivative
    (order : Nat) (time : Real) (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' mode : Int,
    circleHeatWeightRealIteratedDerivative order time fold twist mode

@[simp] theorem circleHeatWeightRealIteratedDerivative_zero
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) :
    circleHeatWeightRealIteratedDerivative 0 time fold twist mode =
      circleHeatWeightReal time fold twist mode := by
  simp [circleHeatWeightRealIteratedDerivative]

@[simp] theorem circleHeatNuclearTraceRealIteratedDerivative_zero
    (time : Real) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTraceRealIteratedDerivative 0 time fold twist =
      circleHeatNuclearTraceReal time fold twist := by
  simp [circleHeatNuclearTraceRealIteratedDerivative,
    circleHeatNuclearTraceReal]

theorem circleHeatWeightRealIteratedDerivative_hasDerivAt
    (order : Nat) (time : Real) (fold : Fold) (twist : CircleTwist)
    (mode : Int) :
    HasDerivAt
      (fun s : Real =>
        circleHeatWeightRealIteratedDerivative order s fold twist mode)
      (circleHeatWeightRealIteratedDerivative (order + 1)
        time fold twist mode) time := by
  have h := (circleHeatWeightReal_hasDerivAt time fold twist mode).const_mul
    ((-circleOperatorSquaredEigenvalue fold twist mode) ^ order)
  simpa [circleHeatWeightRealIteratedDerivative,
    circleHeatWeightRealDerivative, pow_succ, mul_assoc] using h

theorem circleHeatWeightRealIteratedDerivative_continuous
    (order : Nat) (fold : Fold) (twist : CircleTwist) (mode : Int) :
    Continuous (fun time : Real =>
      circleHeatWeightRealIteratedDerivative order time fold twist mode) := by
  unfold circleHeatWeightRealIteratedDerivative
  exact continuous_const.mul (circleHeatWeightReal_continuous fold twist mode)

theorem circleHeatWeightRealIteratedDerivative_uniform_summable
    (order : Nat) (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : Int =>
      spectralAbsorptionConstant order epsilon.1 *
        circleHeatWeightReal (spectralAbsorptionTime order epsilon.1)
          fold twist mode) := by
  exact Summable.mul_left _ (circleHeatWeightReal_uniform_summable
    ⟨spectralAbsorptionTime order epsilon.1,
      spectralAbsorptionTime_pos order epsilon.2⟩ fold twist)

theorem circleHeatWeightRealIteratedDerivative_norm_le
    (order : Nat) (epsilon : HeatTime) {time : Real}
    (hTime : epsilon.1 ≤ time) (fold : Fold) (twist : CircleTwist)
    (mode : Int) :
    ‖circleHeatWeightRealIteratedDerivative order time fold twist mode‖ ≤
      spectralAbsorptionConstant order epsilon.1 *
        circleHeatWeightReal (spectralAbsorptionTime order epsilon.1)
          fold twist mode := by
  have hSpectrum := circleOperatorSquaredEigenvalue_nonnegative fold twist mode
  have hWeight : 0 ≤ circleHeatWeightReal time fold twist mode := by
    unfold circleHeatWeightReal
    exact (Real.exp_pos _).le
  rw [circleHeatWeightRealIteratedDerivative, Real.norm_eq_abs, abs_mul,
    abs_pow, abs_neg, abs_of_nonneg hSpectrum, abs_of_nonneg hWeight]
  refine (mul_le_mul_of_nonneg_left
    (circleHeatWeightReal_le_of_le hTime fold twist mode)
    (pow_nonneg hSpectrum order)).trans ?_
  unfold circleHeatWeightReal
  exact spectralFactor_pow_mul_exp_bound order epsilon.2 hSpectrum

theorem circleHeatWeightRealIteratedDerivative_summable
    (order : Nat) (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : Int =>
      circleHeatWeightRealIteratedDerivative order time.1 fold twist mode) := by
  apply Summable.of_norm_bounded
    (circleHeatWeightRealIteratedDerivative_uniform_summable
      order time fold twist)
  intro mode
  exact circleHeatWeightRealIteratedDerivative_norm_le
    order time le_rfl fold twist mode

theorem circleHeatNuclearTraceRealIteratedDerivative_continuousOn_Ici
    (order : Nat) (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceRealIteratedDerivative order time fold twist)
      (Ici epsilon.1) := by
  unfold circleHeatNuclearTraceRealIteratedDerivative
  apply continuousOn_tsum
  · intro mode
    exact (circleHeatWeightRealIteratedDerivative_continuous
      order fold twist mode).continuousOn
  · exact circleHeatWeightRealIteratedDerivative_uniform_summable
      order epsilon fold twist
  · intro mode time hTime
    exact circleHeatWeightRealIteratedDerivative_norm_le
      order epsilon hTime fold twist mode

theorem circleHeatNuclearTraceRealIteratedDerivative_continuousOn_Ioi
    (order : Nat) (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceRealIteratedDerivative order time fold twist)
      (Ioi 0) := by
  intro time hTime
  let epsilon : HeatTime := ⟨time / 2, half_pos hTime⟩
  have hLocal := circleHeatNuclearTraceRealIteratedDerivative_continuousOn_Ici
    order epsilon fold twist
  exact (hLocal.continuousAt
    (Ici_mem_nhds (half_lt_self hTime))).continuousWithinAt

theorem circleHeatNuclearTraceRealIteratedDerivative_hasDerivAt
    (order : Nat) (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    HasDerivAt
      (fun s : Real =>
        circleHeatNuclearTraceRealIteratedDerivative order s fold twist)
      (circleHeatNuclearTraceRealIteratedDerivative (order + 1)
        time.1 fold twist) time.1 := by
  unfold circleHeatNuclearTraceRealIteratedDerivative
  let epsilon : HeatTime := ⟨time.1 / 2, half_pos time.2⟩
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun mode s =>
      circleHeatWeightRealIteratedDerivative order s fold twist mode)
    (g' := fun mode s =>
      circleHeatWeightRealIteratedDerivative (order + 1) s fold twist mode)
    (u := fun mode : Int =>
      spectralAbsorptionConstant (order + 1) epsilon.1 *
        circleHeatWeightReal (spectralAbsorptionTime (order + 1) epsilon.1)
          fold twist mode)
    (t := Ioi epsilon.1) (y₀ := time.1) (y := time.1)
  · exact circleHeatWeightRealIteratedDerivative_uniform_summable
      (order + 1) epsilon fold twist
  · exact isOpen_Ioi
  · exact isPreconnected_Ioi
  · intro mode s _
    exact circleHeatWeightRealIteratedDerivative_hasDerivAt
      order s fold twist mode
  · intro mode s hs
    exact circleHeatWeightRealIteratedDerivative_norm_le
      (order + 1) epsilon hs.le fold twist mode
  · exact mem_Ioi.mpr (half_lt_self time.2)
  · exact circleHeatWeightRealIteratedDerivative_summable
      order time fold twist
  · exact mem_Ioi.mpr (half_lt_self time.2)

theorem circleHeatNuclearTraceRealIteratedDerivative_deriv_eq
    (order : Nat) (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    deriv (fun s : Real =>
      circleHeatNuclearTraceRealIteratedDerivative order s fold twist) time.1 =
        circleHeatNuclearTraceRealIteratedDerivative (order + 1)
          time.1 fold twist :=
  (circleHeatNuclearTraceRealIteratedDerivative_hasDerivAt
    order time fold twist).deriv

theorem circleHeatNuclearTraceRealIteratedDerivative_alternating_nonnegative
    (order : Nat) (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    0 ≤ (-1 : Real) ^ order *
      circleHeatNuclearTraceRealIteratedDerivative order time.1 fold twist := by
  rw [circleHeatNuclearTraceRealIteratedDerivative, ← tsum_mul_left]
  apply tsum_nonneg
  intro mode
  rw [circleHeatWeightRealIteratedDerivative]
  have hSpectrum := circleOperatorSquaredEigenvalue_nonnegative fold twist mode
  have hWeight : 0 ≤ circleHeatWeightReal time.1 fold twist mode := by
    unfold circleHeatWeightReal
    exact (Real.exp_pos _).le
  rw [← mul_assoc, ← mul_pow]
  norm_num
  exact mul_nonneg (pow_nonneg hSpectrum order) hWeight

theorem circleHeatNuclearTraceRealIteratedDerivative_contDiffOn_nat
    (derivativeOrder smoothnessOrder : Nat) (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ smoothnessOrder
      (fun time : Real =>
        circleHeatNuclearTraceRealIteratedDerivative derivativeOrder
          time fold twist)
      (Ioi 0) := by
  induction smoothnessOrder generalizing derivativeOrder with
  | zero =>
      exact contDiffOn_zero.mpr
        (circleHeatNuclearTraceRealIteratedDerivative_continuousOn_Ioi
          derivativeOrder fold twist)
  | succ smoothnessOrder ih =>
      change ContDiffOn ℝ (smoothnessOrder + 1)
        (fun time : Real =>
          circleHeatNuclearTraceRealIteratedDerivative derivativeOrder
            time fold twist) (Ioi 0)
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, ?_, ?_⟩
      · intro time hTime
        exact DifferentiableAt.differentiableWithinAt
          (circleHeatNuclearTraceRealIteratedDerivative_hasDerivAt
            derivativeOrder ⟨time, hTime⟩ fold twist).differentiableAt
      · intro hImpossible
        norm_num at hImpossible
      · exact (ih (derivativeOrder + 1)).congr fun time hTime =>
          circleHeatNuclearTraceRealIteratedDerivative_deriv_eq
            derivativeOrder ⟨time, hTime⟩ fold twist

theorem circleHeatNuclearTraceReal_contDiffOn_infty
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ ∞
      (fun time : Real => circleHeatNuclearTraceReal time fold twist) (Ioi 0) := by
  rw [contDiffOn_infty]
  intro order
  exact (circleHeatNuclearTraceRealIteratedDerivative_contDiffOn_nat
    0 order fold twist).congr fun time _ => by simp

theorem circleHeatNuclearTraceRealIteratedDerivative_pt_eq_positive
    (order : Nat) (time : Real) (twist : CircleTwist) :
    circleHeatNuclearTraceRealIteratedDerivative order time .pt twist =
      circleHeatNuclearTraceRealIteratedDerivative order time .positive twist := by
  unfold circleHeatNuclearTraceRealIteratedDerivative
    circleHeatWeightRealIteratedDerivative
  apply tsum_congr
  intro mode
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    pt_eigenvalueSq_eq_positive,
    circleHeatWeightReal_pt_eq_positive]

end
end P0EFTJanusCircleHeatNuclearTraceSmooth
end JanusFormal

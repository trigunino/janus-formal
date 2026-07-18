import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceContinuity
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Positive-time derivative of the circle nuclear heat trace

The spectral derivative series is uniformly summable on every half-line away
from zero.  Termwise differentiation then identifies the derivative of the
explicit circle nuclear trace.  No global Janus operator family is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatNuclearTraceDerivative

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceContinuity

/-- The modewise time derivative of the real heat coefficient. -/
def circleHeatWeightRealDerivative
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) : Real :=
  -circleOperatorSquaredEigenvalue fold twist mode *
    circleHeatWeightReal time fold twist mode

/-- The convergent spectral expression for the time derivative of the trace. -/
def circleHeatNuclearTraceRealDerivative
    (time : Real) (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' mode : Int, circleHeatWeightRealDerivative time fold twist mode

theorem circleHeatWeightReal_hasDerivAt
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) :
    HasDerivAt (fun s : Real => circleHeatWeightReal s fold twist mode)
      (circleHeatWeightRealDerivative time fold twist mode) time := by
  unfold circleHeatWeightRealDerivative circleHeatWeightReal
  let spectrum := circleOperatorSquaredEigenvalue fold twist mode
  have hInner : HasDerivAt (fun s : Real => -s * spectrum) (-spectrum) time := by
    simpa [mul_comm] using (hasDerivAt_id time).const_mul (-spectrum)
  have hComp := (Real.hasDerivAt_exp (-time * spectrum)).comp time hInner
  have hFunctions :
      (fun s : Real => Real.exp (-s * spectrum)) =ᶠ[nhds time]
        (Real.exp ∘ fun s : Real => -s * spectrum) := by
    filter_upwards [] with s
    rfl
  simpa [spectrum, mul_comm] using hComp.congr_of_eventuallyEq hFunctions

theorem circleHeatWeightRealDerivative_continuous
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    Continuous (fun time : Real =>
      circleHeatWeightRealDerivative time fold twist mode) := by
  unfold circleHeatWeightRealDerivative
  exact continuous_const.mul (circleHeatWeightReal_continuous fold twist mode)

/-- Exponential absorption of one nonnegative spectral factor. -/
theorem spectralFactor_mul_exp_bound
    {epsilon spectrum : Real} (hEpsilon : 0 < epsilon) :
    spectrum * Real.exp (-epsilon * spectrum) ≤
      (2 / epsilon * Real.exp (-1)) *
        Real.exp (-(epsilon / 2) * spectrum) := by
  have hHalf : 0 < epsilon / 2 := half_pos hEpsilon
  have hCore := Real.mul_exp_neg_le_exp_neg_one ((epsilon / 2) * spectrum)
  have hExp : 0 ≤ Real.exp (-(epsilon / 2) * spectrum) := (Real.exp_pos _).le
  have hScaled := mul_le_mul_of_nonneg_right hCore hExp
  have hScale := mul_le_mul_of_nonneg_left hScaled
    (div_nonneg (by norm_num : (0 : Real) ≤ 2) hEpsilon.le)
  have hExpSquare :
      Real.exp (-(epsilon / 2) * spectrum) *
          Real.exp (-(epsilon / 2) * spectrum) =
        Real.exp (-epsilon * spectrum) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    spectrum * Real.exp (-epsilon * spectrum) =
        (2 / epsilon) * (((epsilon / 2) * spectrum) *
          Real.exp (-(epsilon / 2) * spectrum) *
          Real.exp (-(epsilon / 2) * spectrum)) := by
            calc
              _ = spectrum * (Real.exp (-(epsilon / 2) * spectrum) *
                  Real.exp (-(epsilon / 2) * spectrum)) := by rw [hExpSquare]
              _ = _ := by field_simp [hEpsilon.ne']
    _ ≤ (2 / epsilon) * (Real.exp (-1) *
          Real.exp (-(epsilon / 2) * spectrum)) := by
            simpa only [neg_mul] using hScale
    _ = (2 / epsilon * Real.exp (-1)) *
          Real.exp (-(epsilon / 2) * spectrum) := by ring

/-- The derivative coefficients have a summable majorant depending only on
the positive lower time. -/
theorem circleHeatWeightRealDerivative_uniform_summable
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : Int =>
      (2 / epsilon.1 * Real.exp (-1)) *
        circleHeatWeightReal (epsilon.1 / 2) fold twist mode) := by
  exact Summable.mul_left _ (circleHeatWeightReal_uniform_summable
    ⟨epsilon.1 / 2, half_pos epsilon.2⟩ fold twist)

theorem circleHeatWeightRealDerivative_norm_le
    (epsilon : HeatTime) {time : Real} (hTime : epsilon.1 ≤ time)
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    ‖circleHeatWeightRealDerivative time fold twist mode‖ ≤
      (2 / epsilon.1 * Real.exp (-1)) *
        circleHeatWeightReal (epsilon.1 / 2) fold twist mode := by
  have hSpectrum := circleOperatorSquaredEigenvalue_nonnegative fold twist mode
  rw [circleHeatWeightRealDerivative, Real.norm_eq_abs,
    abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hSpectrum)
      (by unfold circleHeatWeightReal; exact (Real.exp_pos _).le)), neg_mul, neg_neg]
  refine (mul_le_mul_of_nonneg_left
    (circleHeatWeightReal_le_of_le hTime fold twist mode) hSpectrum).trans ?_
  unfold circleHeatWeightReal
  exact spectralFactor_mul_exp_bound epsilon.2

/-- The spectral derivative series is continuous uniformly away from time
zero. -/
theorem circleHeatNuclearTraceRealDerivative_continuousOn_Ici
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceRealDerivative time fold twist) (Ici epsilon.1) := by
  unfold circleHeatNuclearTraceRealDerivative
  apply continuousOn_tsum
  · intro mode
    exact (circleHeatWeightRealDerivative_continuous fold twist mode).continuousOn
  · exact circleHeatWeightRealDerivative_uniform_summable epsilon fold twist
  · intro mode time hTime
    exact circleHeatWeightRealDerivative_norm_le epsilon hTime fold twist mode

/-- For every positive time, the derivative of the explicit nuclear trace is
the convergent sum of the modewise spectral derivatives. -/
theorem circleHeatNuclearTraceReal_hasDerivAt
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    HasDerivAt (fun s : Real => circleHeatNuclearTraceReal s fold twist)
      (circleHeatNuclearTraceRealDerivative time.1 fold twist)
      time.1 := by
  unfold circleHeatNuclearTraceReal circleHeatNuclearTraceRealDerivative
  let epsilon : HeatTime := ⟨time.1 / 2, half_pos time.2⟩
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun mode s => circleHeatWeightReal s fold twist mode)
    (g' := fun mode s => circleHeatWeightRealDerivative s fold twist mode)
    (u := fun mode : Int =>
      (2 / epsilon.1 * Real.exp (-1)) *
        circleHeatWeightReal (epsilon.1 / 2) fold twist mode)
    (t := Ioi epsilon.1) (y₀ := time.1) (y := time.1)
  · exact circleHeatWeightRealDerivative_uniform_summable epsilon fold twist
  · exact isOpen_Ioi
  · exact isPreconnected_Ioi
  · intro mode s _
    exact circleHeatWeightReal_hasDerivAt s fold twist mode
  · intro mode s hs
    exact circleHeatWeightRealDerivative_norm_le epsilon hs.le fold twist mode
  · exact mem_Ioi.mpr (half_lt_self time.2)
  · simpa only [circleHeatWeightReal_of_heatTime] using
      circleOperatorHeatWeight_summable time fold twist
  · exact mem_Ioi.mpr (half_lt_self time.2)

theorem circleHeatNuclearTraceReal_deriv_eq
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    deriv (fun s : Real => circleHeatNuclearTraceReal s fold twist) time.1 =
      circleHeatNuclearTraceRealDerivative time.1 fold twist :=
  (circleHeatNuclearTraceReal_hasDerivAt time fold twist).deriv

theorem circleHeatWeightRealDerivative_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : Int =>
      circleHeatWeightRealDerivative time.1 fold twist mode) := by
  apply Summable.of_norm_bounded
    (circleHeatWeightRealDerivative_uniform_summable time fold twist)
  intro mode
  exact circleHeatWeightRealDerivative_norm_le time le_rfl fold twist mode

theorem circleHeatNuclearTraceRealDerivative_nonpositive
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTraceRealDerivative time.1 fold twist ≤ 0 := by
  unfold circleHeatNuclearTraceRealDerivative
  apply tsum_nonpos
  intro mode
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr
      (circleOperatorSquaredEigenvalue_nonnegative fold twist mode))
    (by unfold circleHeatWeightReal; exact (Real.exp_pos _).le)

theorem circleHeatNuclearTraceReal_deriv_nonpositive
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    deriv (fun s : Real => circleHeatNuclearTraceReal s fold twist) time.1 ≤ 0 := by
  rw [circleHeatNuclearTraceReal_deriv_eq time fold twist]
  exact circleHeatNuclearTraceRealDerivative_nonpositive time fold twist

/-- On every positive closed half-line, the actual derivative of the nuclear
trace is continuous. -/
theorem circleHeatNuclearTraceReal_deriv_continuousOn_Ici
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      deriv (fun s : Real => circleHeatNuclearTraceReal s fold twist) time)
      (Ici epsilon.1) := by
  apply (circleHeatNuclearTraceRealDerivative_continuousOn_Ici
    epsilon fold twist).congr
  intro time hTime
  exact circleHeatNuclearTraceReal_deriv_eq
    ⟨time, epsilon.2.trans_le hTime⟩ fold twist

/-- PT preserves the differentiated nuclear trace. -/
theorem circleHeatNuclearTraceRealDerivative_pt_eq_positive
    (time : Real) (twist : CircleTwist) :
    circleHeatNuclearTraceRealDerivative time .pt twist =
      circleHeatNuclearTraceRealDerivative time .positive twist := by
  unfold circleHeatNuclearTraceRealDerivative
  apply tsum_congr
  intro mode
  unfold circleHeatWeightRealDerivative
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    pt_eigenvalueSq_eq_positive,
    circleHeatWeightReal_pt_eq_positive]

end
end P0EFTJanusCircleHeatNuclearTraceDerivative
end JanusFormal

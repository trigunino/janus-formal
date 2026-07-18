import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceClass
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Positive-time continuity of the circle nuclear heat trace

On every closed half-line `t ≥ ε > 0`, each heat coefficient and each
rank-one operator norm is dominated by the summable coefficient at `ε`.
Consequently the explicit nuclear trace is continuous there.  PT invariance is
preserved throughout.  This is confined to the normalized circle model; no
global Janus Fredholm family or trace-class API is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatNuclearTraceContinuity

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceClass

/-- Heat coefficient with an unrestricted real time parameter. -/
def circleHeatWeightReal
    (time : Real) (fold : Fold) (twist : CircleTwist) (mode : Int) : Real :=
  Real.exp (-time * circleOperatorSquaredEigenvalue fold twist mode)

theorem circleHeatWeightReal_of_heatTime
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : Int) :
    circleHeatWeightReal time fold twist mode =
      circleOperatorHeatWeight time fold twist mode :=
  rfl

theorem circleOperatorSquaredEigenvalue_nonnegative
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    0 ≤ circleOperatorSquaredEigenvalue fold twist mode := by
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  exact eigenvalueSq_nonnegative fold twist mode

/-- Later positive times are dominated modewise by the fixed lower time. -/
theorem circleHeatWeightReal_le_of_le
    {lower time : Real} (hTime : lower ≤ time)
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    circleHeatWeightReal time fold twist mode ≤
      circleHeatWeightReal lower fold twist mode := by
  apply Real.exp_le_exp.mpr
  have hSpectrum := circleOperatorSquaredEigenvalue_nonnegative fold twist mode
  nlinarith

/-- Uniform summable majorant for all scalar heat coefficients on
`[ε,∞)`. -/
theorem circleHeatWeightReal_uniform_summable
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : Int => circleHeatWeightReal epsilon fold twist mode) := by
  simpa only [circleHeatWeightReal_of_heatTime] using
    circleOperatorHeatWeight_summable epsilon fold twist

/-- The rank-one nuclear components at any later time are uniformly dominated
by the summable scalar coefficients at `epsilon`. -/
theorem circleHeatRankOne_uniform_opNorm_le
    (epsilon time : HeatTime) (hTime : epsilon.1 ≤ time.1)
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    ‖circleHeatRankOne time fold twist mode‖ ≤
      circleOperatorHeatWeight epsilon fold twist mode := by
  exact (circleHeatRankOne_opNorm_le time fold twist mode).trans
    (by
      rw [← circleHeatWeightReal_of_heatTime,
        ← circleHeatWeightReal_of_heatTime]
      exact circleHeatWeightReal_le_of_le hTime fold twist mode)

/-- Real-time extension of the explicit nuclear trace. -/
def circleHeatNuclearTraceReal
    (time : Real) (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' mode : Int, circleHeatWeightReal time fold twist mode

theorem circleHeatNuclearTraceReal_of_heatTime
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTraceReal time fold twist =
      circleHeatNuclearTrace time fold twist := by
  unfold circleHeatNuclearTraceReal circleHeatNuclearTrace
  apply tsum_congr
  intro mode
  exact circleHeatWeightReal_of_heatTime time fold twist mode

theorem circleHeatWeightReal_continuous
    (fold : Fold) (twist : CircleTwist) (mode : Int) :
    Continuous (fun time : Real => circleHeatWeightReal time fold twist mode) := by
  unfold circleHeatWeightReal
  fun_prop

/-- The explicit nuclear trace is continuous uniformly away from time zero. -/
theorem circleHeatNuclearTraceReal_continuousOn_Ici
    (epsilon : HeatTime) (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      circleHeatNuclearTraceReal time fold twist) (Ici epsilon.1) := by
  unfold circleHeatNuclearTraceReal
  apply continuousOn_tsum
  · intro mode
    exact (circleHeatWeightReal_continuous fold twist mode).continuousOn
  · exact circleHeatWeightReal_uniform_summable epsilon fold twist
  · intro mode time hTime
    have hNonnegative : 0 ≤ circleHeatWeightReal time fold twist mode := by
      unfold circleHeatWeightReal
      exact (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hNonnegative]
    exact circleHeatWeightReal_le_of_le hTime fold twist mode

/-- PT preserves every real-time heat coefficient. -/
theorem circleHeatWeightReal_pt_eq_positive
    (time : Real) (twist : CircleTwist) (mode : Int) :
    circleHeatWeightReal time .pt twist mode =
      circleHeatWeightReal time .positive twist mode := by
  unfold circleHeatWeightReal
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    pt_eigenvalueSq_eq_positive]

/-- PT preserves the whole continuous real-time nuclear trace family. -/
theorem circleHeatNuclearTraceReal_pt_eq_positive
    (time : Real) (twist : CircleTwist) :
    circleHeatNuclearTraceReal time .pt twist =
      circleHeatNuclearTraceReal time .positive twist := by
  unfold circleHeatNuclearTraceReal
  apply tsum_congr
  exact fun mode => circleHeatWeightReal_pt_eq_positive time twist mode

end
end P0EFTJanusCircleHeatNuclearTraceContinuity
end JanusFormal

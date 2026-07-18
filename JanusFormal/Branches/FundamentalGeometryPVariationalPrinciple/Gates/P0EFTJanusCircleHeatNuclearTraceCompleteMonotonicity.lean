import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceSmooth
import Mathlib.Analysis.Convex.Deriv

/-!
# Complete monotonicity of the positive-time circle heat trace

The arbitrary-order spectral derivatives are identified with Lean's
`iteratedDeriv`.  Their alternating positivity packages complete monotonicity
and yields global antitonicity and convexity on the positive-time interval.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatNuclearTraceCompleteMonotonicity

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceDerivative
open P0EFTJanusCircleHeatNuclearTraceSecondDerivative
open P0EFTJanusCircleHeatNuclearTraceSmooth

def CompletelyMonotoneOnPositive (function : Real → Real) : Prop :=
  ContDiffOn ℝ ∞ function (Ioi 0) ∧
    ∀ order : Nat, ∀ ⦃time : Real⦄, 0 < time →
      0 ≤ (-1 : Real) ^ order * iteratedDeriv order function time

theorem circleHeatNuclearTraceReal_iteratedDeriv_eq
    (order : Nat) (fold : Fold) (twist : CircleTwist) :
    ∀ ⦃time : Real⦄, 0 < time →
      iteratedDeriv order
          (fun s : Real => circleHeatNuclearTraceReal s fold twist) time =
        circleHeatNuclearTraceRealIteratedDerivative order time fold twist := by
  induction order with
  | zero =>
      intro time _
      simp
  | succ order ih =>
      intro time hTime
      rw [iteratedDeriv_succ]
      have hEventually :
          iteratedDeriv order
              (fun s : Real => circleHeatNuclearTraceReal s fold twist) =ᶠ[nhds time]
            fun s : Real =>
              circleHeatNuclearTraceRealIteratedDerivative order s fold twist := by
        filter_upwards [Ioi_mem_nhds hTime] with parameter hParameter
        exact ih hParameter
      rw [hEventually.deriv_eq]
      exact circleHeatNuclearTraceRealIteratedDerivative_deriv_eq
        order ⟨time, hTime⟩ fold twist

theorem circleHeatNuclearTraceReal_completelyMonotoneOnPositive
    (fold : Fold) (twist : CircleTwist) :
    CompletelyMonotoneOnPositive
      (fun time : Real => circleHeatNuclearTraceReal time fold twist) := by
  constructor
  · exact circleHeatNuclearTraceReal_contDiffOn_infty fold twist
  · intro order time hTime
    rw [circleHeatNuclearTraceReal_iteratedDeriv_eq
      order fold twist hTime]
    exact circleHeatNuclearTraceRealIteratedDerivative_alternating_nonnegative
      order ⟨time, hTime⟩ fold twist

theorem circleHeatNuclearTraceReal_antitoneOn_positive
    (fold : Fold) (twist : CircleTwist) :
    AntitoneOn (fun time : Real => circleHeatNuclearTraceReal time fold twist)
      (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : Real))
  · exact (circleHeatNuclearTraceReal_contDiffOn_infty
      fold twist).continuousOn
  · intro time hTime
    rw [interior_Ioi] at hTime
    exact (circleHeatNuclearTraceReal_hasDerivAt
      ⟨time, hTime⟩ fold twist).differentiableAt.differentiableWithinAt
  · intro time hTime
    rw [interior_Ioi] at hTime
    rw [circleHeatNuclearTraceReal_deriv_eq ⟨time, hTime⟩ fold twist]
    exact circleHeatNuclearTraceRealDerivative_nonpositive
      ⟨time, hTime⟩ fold twist

theorem circleHeatNuclearTraceReal_convexOn_positive
    (fold : Fold) (twist : CircleTwist) :
    ConvexOn ℝ (Ioi 0)
      (fun time : Real => circleHeatNuclearTraceReal time fold twist) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (D := Ioi (0 : Real))
    (f' := fun time => circleHeatNuclearTraceRealDerivative time fold twist)
    (f'' := fun time => circleHeatNuclearTraceRealSecondDerivative time fold twist)
    (convex_Ioi (0 : Real))
  · exact (circleHeatNuclearTraceReal_contDiffOn_infty
      fold twist).continuousOn
  · intro time hTime
    rw [interior_Ioi] at hTime
    exact (circleHeatNuclearTraceReal_hasDerivAt
      ⟨time, hTime⟩ fold twist).hasDerivWithinAt
  · intro time hTime
    rw [interior_Ioi] at hTime
    exact (circleHeatNuclearTraceRealDerivative_hasDerivAt
      ⟨time, hTime⟩ fold twist).hasDerivWithinAt
  · intro time hTime
    rw [interior_Ioi] at hTime
    exact circleHeatNuclearTraceRealSecondDerivative_nonnegative
      ⟨time, hTime⟩ fold twist

end
end P0EFTJanusCircleHeatNuclearTraceCompleteMonotonicity
end JanusFormal

import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceCyclicity4D

/-!
# Bounded composition of nuclear rank-one expansions

The cyclicity packet accepts aligned presentations of `B T` and `T B`.  This
file constructs those presentations from one nuclear rank-one expansion of
`T` and one bounded operator `B`.

On the left,

```text
B (rankOne x y) = rankOne (B x) y.
```

On the right,

```text
(rankOne x y) B = rankOne x (B† y).
```

The operator norm of `B` controls both transformed nuclear-norm series.  The
trace series are summable by Cauchy--Schwarz.  Mapping the original operator
series through the continuous bilinear composition map proves the two new
operator equalities.  Thus intrinsic cyclicity no longer requires separately
supplied composition expansions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceCyclicity4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

namespace SummableRankOneOperatorExpansion

/-- The right composition of a rank-one operator is obtained by applying the
adjoint to its covector. -/
theorem rankOne_comp_eq_rankOne_adjoint
    (left right : E) (bounded : E →L[Real] E) :
    (InnerProductSpace.rankOne Real left right).comp bounded =
      InnerProductSpace.rankOne Real left
        (ContinuousLinearMap.adjoint bounded right) := by
  ext vector
  simp [InnerProductSpace.rankOne_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- Nuclear-norm summability after composition on the left. -/
theorem compLeft_nuclearNorm_summable
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    Summable (fun index =>
      |expansion.coefficient index| *
        ‖bounded (expansion.leftVector index)‖ *
          ‖expansion.rightVector index‖) := by
  have hMajorant : Summable (fun index =>
      ‖bounded‖ *
        (|expansion.coefficient index| * ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖)) :=
    expansion.summable_nuclearNorm.mul_left ‖bounded‖
  exact hMajorant.of_nonneg_of_le
    (fun _ => by positivity)
    (fun index => by
      calc
        |expansion.coefficient index| *
              ‖bounded (expansion.leftVector index)‖ *
              ‖expansion.rightVector index‖ ≤
            |expansion.coefficient index| *
              (‖bounded‖ * ‖expansion.leftVector index‖) *
              ‖expansion.rightVector index‖ := by
          gcongr
          exact bounded.le_opNorm _
        _ = ‖bounded‖ *
            (|expansion.coefficient index| *
              ‖expansion.leftVector index‖ *
                ‖expansion.rightVector index‖) := by ring)

/-- Trace summability after composition on the left. -/
theorem compLeft_trace_summable
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    Summable (fun index =>
      expansion.coefficient index *
        inner Real (bounded (expansion.leftVector index))
          (expansion.rightVector index)) := by
  apply Summable.of_norm_bounded
    (expansion.compLeft_nuclearNorm_summable bounded)
  intro index
  rw [norm_mul, Real.norm_eq_abs]
  calc
    |expansion.coefficient index| *
        ‖inner Real (bounded (expansion.leftVector index))
          (expansion.rightVector index)‖ ≤
      |expansion.coefficient index| *
        (‖bounded (expansion.leftVector index)‖ *
          ‖expansion.rightVector index‖) := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = |expansion.coefficient index| *
        ‖bounded (expansion.leftVector index)‖ *
          ‖expansion.rightVector index‖ := by ring

/-- Operator-series identity after composition on the left. -/
theorem compLeft_operator_eq_tsum
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    bounded.comp nuclear = ∑' index,
      expansion.coefficient index •
        InnerProductSpace.rankOne Real
          (bounded (expansion.leftVector index))
          (expansion.rightVector index) := by
  have hSummable : Summable expansion.component :=
    Summable.of_norm expansion.component_norm_summable
  have hOperator : nuclear = ∑' index, expansion.component index := by
    simpa [SummableRankOneOperatorExpansion.component] using
      expansion.operator_eq_tsum
  calc
    bounded.comp nuclear =
        (ContinuousLinearMap.compL Real E E E bounded) nuclear := rfl
    _ = (ContinuousLinearMap.compL Real E E E bounded)
        (∑' index, expansion.component index) := by rw [hOperator]
    _ = ∑' index,
        (ContinuousLinearMap.compL Real E E E bounded)
          (expansion.component index) :=
      (ContinuousLinearMap.compL Real E E E bounded).map_tsum hSummable
    _ = ∑' index,
        expansion.coefficient index •
          InnerProductSpace.rankOne Real
            (bounded (expansion.leftVector index))
            (expansion.rightVector index) := by
      apply tsum_congr
      intro index
      ext vector
      simp [SummableRankOneOperatorExpansion.component,
        InnerProductSpace.rankOne_apply]

/-- Nuclear-norm summability after composition on the right. -/
theorem compRight_nuclearNorm_summable
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    Summable (fun index =>
      |expansion.coefficient index| * ‖expansion.leftVector index‖ *
        ‖ContinuousLinearMap.adjoint bounded
          (expansion.rightVector index)‖) := by
  have hMajorant : Summable (fun index =>
      ‖bounded‖ *
        (|expansion.coefficient index| * ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖)) :=
    expansion.summable_nuclearNorm.mul_left ‖bounded‖
  exact hMajorant.of_nonneg_of_le
    (fun _ => by positivity)
    (fun index => by
      have hAdjoint :
          ‖ContinuousLinearMap.adjoint bounded
              (expansion.rightVector index)‖ ≤
            ‖bounded‖ * ‖expansion.rightVector index‖ := by
        calc
          ‖ContinuousLinearMap.adjoint bounded
              (expansion.rightVector index)‖ ≤
              ‖ContinuousLinearMap.adjoint bounded‖ *
                ‖expansion.rightVector index‖ :=
            (ContinuousLinearMap.adjoint bounded).le_opNorm _
          _ = ‖bounded‖ * ‖expansion.rightVector index‖ := by
            rw [ContinuousLinearMap.adjoint.norm_map]
      calc
        |expansion.coefficient index| * ‖expansion.leftVector index‖ *
              ‖ContinuousLinearMap.adjoint bounded
                (expansion.rightVector index)‖ ≤
            |expansion.coefficient index| * ‖expansion.leftVector index‖ *
              (‖bounded‖ * ‖expansion.rightVector index‖) := by
          gcongr
        _ = ‖bounded‖ *
            (|expansion.coefficient index| *
              ‖expansion.leftVector index‖ *
                ‖expansion.rightVector index‖) := by ring)

/-- Trace summability after composition on the right. -/
theorem compRight_trace_summable
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    Summable (fun index =>
      expansion.coefficient index *
        inner Real (expansion.leftVector index)
          (ContinuousLinearMap.adjoint bounded
            (expansion.rightVector index))) := by
  apply Summable.of_norm_bounded
    (expansion.compRight_nuclearNorm_summable bounded)
  intro index
  rw [norm_mul, Real.norm_eq_abs]
  calc
    |expansion.coefficient index| *
        ‖inner Real (expansion.leftVector index)
          (ContinuousLinearMap.adjoint bounded
            (expansion.rightVector index))‖ ≤
      |expansion.coefficient index| *
        (‖expansion.leftVector index‖ *
          ‖ContinuousLinearMap.adjoint bounded
            (expansion.rightVector index)‖) := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = |expansion.coefficient index| * ‖expansion.leftVector index‖ *
        ‖ContinuousLinearMap.adjoint bounded
          (expansion.rightVector index)‖ := by ring

/-- Operator-series identity after composition on the right. -/
theorem compRight_operator_eq_tsum
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    nuclear.comp bounded = ∑' index,
      expansion.coefficient index •
        InnerProductSpace.rankOne Real
          (expansion.leftVector index)
          (ContinuousLinearMap.adjoint bounded
            (expansion.rightVector index)) := by
  have hSummable : Summable expansion.component :=
    Summable.of_norm expansion.component_norm_summable
  have hOperator : nuclear = ∑' index, expansion.component index := by
    simpa [SummableRankOneOperatorExpansion.component] using
      expansion.operator_eq_tsum
  let rightComposition :
      (E →L[Real] E) →L[Real] (E →L[Real] E) :=
    (ContinuousLinearMap.compL Real E E E).flip bounded
  calc
    nuclear.comp bounded = rightComposition nuclear := rfl
    _ = rightComposition (∑' index, expansion.component index) := by
      rw [hOperator]
    _ = ∑' index, rightComposition (expansion.component index) :=
      rightComposition.map_tsum hSummable
    _ = ∑' index,
        expansion.coefficient index •
          InnerProductSpace.rankOne Real
            (expansion.leftVector index)
            (ContinuousLinearMap.adjoint bounded
              (expansion.rightVector index)) := by
      apply tsum_congr
      intro index
      ext vector
      simp [rightComposition, SummableRankOneOperatorExpansion.component,
        InnerProductSpace.rankOne_apply,
        ContinuousLinearMap.adjoint_inner_left]

/-- Nuclear expansion of `B T` generated from an expansion of `T`. -/
def compLeft
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    SummableRankOneOperatorExpansion (bounded.comp nuclear) where
  Index := expansion.Index
  coefficient := expansion.coefficient
  leftVector := fun index => bounded (expansion.leftVector index)
  rightVector := expansion.rightVector
  summable_nuclearNorm := expansion.compLeft_nuclearNorm_summable bounded
  trace_summable := expansion.compLeft_trace_summable bounded
  operator_eq_tsum := expansion.compLeft_operator_eq_tsum bounded

/-- Nuclear expansion of `T B` generated from an expansion of `T`. -/
def compRight
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    SummableRankOneOperatorExpansion (nuclear.comp bounded) where
  Index := expansion.Index
  coefficient := expansion.coefficient
  leftVector := expansion.leftVector
  rightVector := fun index =>
    ContinuousLinearMap.adjoint bounded (expansion.rightVector index)
  summable_nuclearNorm := expansion.compRight_nuclearNorm_summable bounded
  trace_summable := expansion.compRight_trace_summable bounded
  operator_eq_tsum := expansion.compRight_operator_eq_tsum bounded

/-- Automatic aligned cyclicity presentation generated by one expansion of
`T`. -/
def toCyclicCompositionData
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E) :
    CyclicNuclearCompositionExpansionData nuclear bounded where
  Index := expansion.Index
  coefficient := expansion.coefficient
  leftVector := expansion.leftVector
  rightVector := expansion.rightVector
  left_nuclearNorm_summable := expansion.compLeft_nuclearNorm_summable bounded
  right_nuclearNorm_summable := expansion.compRight_nuclearNorm_summable bounded
  left_trace_summable := expansion.compLeft_trace_summable bounded
  right_trace_summable := expansion.compRight_trace_summable bounded
  left_operator_eq_tsum := expansion.compLeft_operator_eq_tsum bounded
  right_operator_eq_tsum := expansion.compRight_operator_eq_tsum bounded

/-- Intrinsic cyclicity from one nuclear presentation and two intrinsic trace
certificates for the compositions. -/
theorem intrinsicNuclearTrace_comp_comm_of_expansion
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E)
    (leftTrace : IntrinsicNuclearTraceData (bounded.comp nuclear))
    (rightTrace : IntrinsicNuclearTraceData (nuclear.comp bounded)) :
    intrinsicNuclearTrace leftTrace = intrinsicNuclearTrace rightTrace :=
  (expansion.toCyclicCompositionData bounded).
    intrinsicNuclearTrace_comp_comm leftTrace rightTrace

end SummableRankOneOperatorExpansion

/-- Public bounded-composition cyclicity checkpoint. -/
theorem intrinsic_nuclear_trace_bounded_composition_gate
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion nuclear)
    (bounded : E →L[Real] E)
    (leftTrace : IntrinsicNuclearTraceData (bounded.comp nuclear))
    (rightTrace : IntrinsicNuclearTraceData (nuclear.comp bounded)) :
    intrinsicNuclearTrace leftTrace = intrinsicNuclearTrace rightTrace :=
  expansion.intrinsicNuclearTrace_comp_comm_of_expansion bounded
    leftTrace rightTrace

end
end P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
end JanusFormal

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

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

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
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
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
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E) :
    Summable (fun index =>
      expansion.coefficient index *
        inner Real (bounded (expansion.leftVector index))
          (expansion.rightVector index)) := by
  apply Summable.of_norm_bounded
    (compLeft_nuclearNorm_summable expansion bounded)
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
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
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
        (∑' index, expansion.component index) :=
      congrArg (ContinuousLinearMap.compL Real E E E bounded) hOperator
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
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
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
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E) :
    Summable (fun index =>
      expansion.coefficient index *
        inner Real (expansion.leftVector index)
          (ContinuousLinearMap.adjoint bounded
            (expansion.rightVector index))) := by
  apply Summable.of_norm_bounded
    (compRight_nuclearNorm_summable expansion bounded)
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
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
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
    _ = rightComposition (∑' index, expansion.component index) :=
      congrArg rightComposition hOperator
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
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E) :
    SummableRankOneOperatorExpansion (bounded.comp nuclear) where
  Index := expansion.Index
  coefficient := expansion.coefficient
  leftVector := fun index => bounded (expansion.leftVector index)
  rightVector := expansion.rightVector
  summable_nuclearNorm := compLeft_nuclearNorm_summable expansion bounded
  trace_summable := compLeft_trace_summable expansion bounded
  operator_eq_tsum := compLeft_operator_eq_tsum expansion bounded

/-- The trace of `B T` is bounded by the operator norm of `B` times the
nuclear-norm sum of any rank-one presentation of `T`. -/
theorem compLeft_expansionTrace_abs_le_nuclearNormSum
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E) :
    |(compLeft expansion bounded).expansionTrace| ≤
      ‖bounded‖ * ∑' index,
        |expansion.coefficient index| * ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖ := by
  change
    |∑' index,
      expansion.coefficient index *
        inner Real (bounded (expansion.leftVector index))
          (expansion.rightVector index)| ≤ _
  rw [← Real.norm_eq_abs]
  have hMajorant : Summable (fun index =>
      ‖bounded‖ *
        (|expansion.coefficient index| * ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖)) :=
    expansion.summable_nuclearNorm.mul_left ‖bounded‖
  calc
    ‖∑' index,
        expansion.coefficient index *
          inner Real (bounded (expansion.leftVector index))
            (expansion.rightVector index)‖ ≤
        ∑' index, ‖bounded‖ *
          (|expansion.coefficient index| * ‖expansion.leftVector index‖ *
            ‖expansion.rightVector index‖) := by
      exact tsum_of_norm_bounded hMajorant.hasSum fun index => by
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
          _ ≤ ‖bounded‖ *
              (|expansion.coefficient index| * ‖expansion.leftVector index‖ *
                ‖expansion.rightVector index‖) := by
            calc
              _ ≤ |expansion.coefficient index| *
                    ((‖bounded‖ * ‖expansion.leftVector index‖) *
                      ‖expansion.rightVector index‖) := by
                  gcongr
                  exact bounded.le_opNorm _
              _ = _ := by ring
    _ = ‖bounded‖ * ∑' index,
        |expansion.coefficient index| * ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖ := by
      rw [tsum_mul_left]

/-- Intrinsic version of the bounded-composition trace estimate. -/
theorem intrinsicNuclearTrace_compLeft_abs_le_nuclearNormSum
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E)
    (trace : IntrinsicNuclearTraceData.{v, u} (bounded.comp nuclear)) :
    |intrinsicNuclearTrace trace| ≤
      ‖bounded‖ * ∑' index,
        |expansion.coefficient index| * ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖ := by
  rw [← trace.expansionTrace_eq (compLeft expansion bounded)]
  exact compLeft_expansionTrace_abs_le_nuclearNormSum expansion bounded

/-- If the nuclear-norm sum is controlled by a positive heat trace and
`B` has a prescribed norm bound, then `|Tr(B T)|` has the expected heat-trace
bound. -/
theorem intrinsicNuclearTrace_compLeft_abs_le_heatTrace
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E)
    (trace : IntrinsicNuclearTraceData.{v, u} (bounded.comp nuclear))
    (heatTrace bound : Real)
    (hNuclear :
      (∑' index,
        |expansion.coefficient index| * ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖) ≤ heatTrace)
    (hHeatTrace : 0 ≤ heatTrace)
    (hBound : ‖bounded‖ ≤ bound) :
    |intrinsicNuclearTrace trace| ≤ bound * heatTrace := by
  calc
    |intrinsicNuclearTrace trace| ≤
        ‖bounded‖ * ∑' index,
          |expansion.coefficient index| * ‖expansion.leftVector index‖ *
            ‖expansion.rightVector index‖ :=
      intrinsicNuclearTrace_compLeft_abs_le_nuclearNormSum expansion
        bounded trace
    _ ≤ ‖bounded‖ * heatTrace :=
      mul_le_mul_of_nonneg_left hNuclear (norm_nonneg bounded)
    _ ≤ bound * heatTrace :=
      mul_le_mul_of_nonneg_right hBound hHeatTrace

/-- Nuclear expansion of `T B` generated from an expansion of `T`. -/
def compRight
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E) :
    SummableRankOneOperatorExpansion (nuclear.comp bounded) where
  Index := expansion.Index
  coefficient := expansion.coefficient
  leftVector := expansion.leftVector
  rightVector := fun index =>
    ContinuousLinearMap.adjoint bounded (expansion.rightVector index)
  summable_nuclearNorm := compRight_nuclearNorm_summable expansion bounded
  trace_summable := compRight_trace_summable expansion bounded
  operator_eq_tsum := compRight_operator_eq_tsum expansion bounded

/-- Automatic aligned cyclicity presentation generated by one expansion of
`T`. -/
def toCyclicCompositionData
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E) :
    CyclicNuclearCompositionExpansionData nuclear bounded where
  Index := expansion.Index
  coefficient := expansion.coefficient
  leftVector := expansion.leftVector
  rightVector := expansion.rightVector
  left_nuclearNorm_summable := compLeft_nuclearNorm_summable expansion bounded
  right_nuclearNorm_summable := compRight_nuclearNorm_summable expansion bounded
  left_trace_summable := compLeft_trace_summable expansion bounded
  right_trace_summable := compRight_trace_summable expansion bounded
  left_operator_eq_tsum := compLeft_operator_eq_tsum expansion bounded
  right_operator_eq_tsum := compRight_operator_eq_tsum expansion bounded

/-- Intrinsic cyclicity from one nuclear presentation and two intrinsic trace
certificates for the compositions. -/
theorem intrinsicNuclearTrace_comp_comm_of_expansion
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E)
    (leftTrace : IntrinsicNuclearTraceData.{v, u} (bounded.comp nuclear))
    (rightTrace : IntrinsicNuclearTraceData.{v, u} (nuclear.comp bounded)) :
    intrinsicNuclearTrace leftTrace = intrinsicNuclearTrace rightTrace :=
  CyclicNuclearCompositionExpansionData.intrinsicNuclearTrace_comp_comm
    (toCyclicCompositionData expansion bounded) leftTrace rightTrace

end SummableRankOneOperatorExpansion

/-- Public bounded-composition cyclicity checkpoint. -/
theorem intrinsic_nuclear_trace_bounded_composition_gate
    {nuclear : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{u, v} nuclear)
    (bounded : E →L[Real] E)
    (leftTrace : IntrinsicNuclearTraceData.{v, u} (bounded.comp nuclear))
    (rightTrace : IntrinsicNuclearTraceData.{v, u} (nuclear.comp bounded)) :
    intrinsicNuclearTrace leftTrace = intrinsicNuclearTrace rightTrace :=
  SummableRankOneOperatorExpansion.intrinsicNuclearTrace_comp_comm_of_expansion
    expansion bounded
    leftTrace rightTrace

end
end P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
end JanusFormal

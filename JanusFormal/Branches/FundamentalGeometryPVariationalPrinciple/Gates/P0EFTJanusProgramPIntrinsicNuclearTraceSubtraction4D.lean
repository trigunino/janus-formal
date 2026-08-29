import Mathlib.Topology.Algebra.InfiniteSum.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Intrinsic nuclear trace of an operator difference

Given summable rank-one presentations of `A` and `B`, use the disjoint sum of
index types and negate the coefficients of the second presentation.  This gives
a summable rank-one presentation of

```text
A - B.
```

Presentation independence then forces

```text
Tr(A - B) = Tr(A) - Tr(B).
```

This is the scalar bridge from a relative heat operator to the difference of
its actual and reference heat traces.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

end
end P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
namespace P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
namespace SummableRankOneOperatorExpansion

noncomputable section

open scoped InnerProductSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Disjoint-sum presentation of the difference of two nuclear operators. -/
def sub
    {first second : E →L[Real] E}
    (firstExpansion : SummableRankOneOperatorExpansion first)
    (secondExpansion : SummableRankOneOperatorExpansion second) :
    SummableRankOneOperatorExpansion (first - second) where
  Index := Sum firstExpansion.Index secondExpansion.Index
  coefficient
    | Sum.inl index => firstExpansion.coefficient index
    | Sum.inr index => -secondExpansion.coefficient index
  leftVector
    | Sum.inl index => firstExpansion.leftVector index
    | Sum.inr index => secondExpansion.leftVector index
  rightVector
    | Sum.inl index => firstExpansion.rightVector index
    | Sum.inr index => secondExpansion.rightVector index
  summable_nuclearNorm := by
    refine (Summable.sum
      (α := firstExpansion.Index) (β := secondExpansion.Index) (M := Real)
      (fun index : firstExpansion.Index ⊕ secondExpansion.Index =>
        match index with
        | Sum.inl index => |firstExpansion.coefficient index| *
            ‖firstExpansion.leftVector index‖ * ‖firstExpansion.rightVector index‖
        | Sum.inr index => |secondExpansion.coefficient index| *
            ‖secondExpansion.leftVector index‖ * ‖secondExpansion.rightVector index‖)
      firstExpansion.summable_nuclearNorm
      secondExpansion.summable_nuclearNorm).congr ?_
    intro index
    cases index <;> simp
  trace_summable := by
    refine (Summable.sum
      (α := firstExpansion.Index) (β := secondExpansion.Index) (M := Real)
      (fun index : firstExpansion.Index ⊕ secondExpansion.Index =>
        match index with
        | Sum.inl index => firstExpansion.coefficient index *
            inner Real (firstExpansion.leftVector index) (firstExpansion.rightVector index)
        | Sum.inr index => -(secondExpansion.coefficient index *
            inner Real (secondExpansion.leftVector index) (secondExpansion.rightVector index)))
      firstExpansion.trace_summable secondExpansion.trace_summable.neg).congr ?_
    intro index
    cases index <;> simp
  operator_eq_tsum := by
    have hFirst : Summable firstExpansion.component :=
      Summable.of_norm firstExpansion.component_norm_summable
    have hSecond : Summable secondExpansion.component :=
      Summable.of_norm secondExpansion.component_norm_summable
    have hTsum := Summable.tsum_sum
      (α := firstExpansion.Index) (β := secondExpansion.Index)
      (M := E →L[Real] E)
      (f := fun index : firstExpansion.Index ⊕ secondExpansion.Index =>
        match index with
        | Sum.inl index => firstExpansion.component index
        | Sum.inr index => -secondExpansion.component index)
      hFirst hSecond.neg
    have hDesired : first - second = ∑' index :
        firstExpansion.Index ⊕ secondExpansion.Index, match index with
        | Sum.inl index => firstExpansion.coefficient index •
            InnerProductSpace.rankOne Real (firstExpansion.leftVector index)
              (firstExpansion.rightVector index)
        | Sum.inr index => (-secondExpansion.coefficient index) •
            InnerProductSpace.rankOne Real (secondExpansion.leftVector index)
              (secondExpansion.rightVector index) := by
      calc
        first - second = (∑' index, firstExpansion.component index) -
            ∑' index, secondExpansion.component index :=
          congrArg₂ (· - ·) firstExpansion.operator_eq_tsum
            secondExpansion.operator_eq_tsum
        _ = (∑' index, firstExpansion.component index) +
            ∑' index, -secondExpansion.component index := by
          rw [sub_eq_add_neg, tsum_neg]
        _ = ∑' index : firstExpansion.Index ⊕ secondExpansion.Index,
            match index with
            | Sum.inl index => firstExpansion.coefficient index •
                InnerProductSpace.rankOne Real (firstExpansion.leftVector index)
                  (firstExpansion.rightVector index)
            | Sum.inr index => (-secondExpansion.coefficient index) •
                InnerProductSpace.rankOne Real (secondExpansion.leftVector index)
                  (secondExpansion.rightVector index) := by
          rw [← hTsum]
          apply tsum_congr
          intro index
          cases index <;>
            simp [SummableRankOneOperatorExpansion.component]
    convert hDesired using 1
    apply tsum_congr
    intro index
    cases index <;> rfl

@[simp]
theorem sub_expansionTrace
    {first second : E →L[Real] E}
    (firstExpansion : SummableRankOneOperatorExpansion first)
    (secondExpansion : SummableRankOneOperatorExpansion second) :
    (firstExpansion.sub secondExpansion).expansionTrace =
      firstExpansion.expansionTrace - secondExpansion.expansionTrace := by
  unfold SummableRankOneOperatorExpansion.expansionTrace
    SummableRankOneOperatorExpansion.sub
  have hTsum := Summable.tsum_sum
    (α := firstExpansion.Index) (β := secondExpansion.Index) (M := Real)
    (f := fun index : firstExpansion.Index ⊕ secondExpansion.Index =>
      match index with
      | Sum.inl index => firstExpansion.coefficient index *
          inner Real (firstExpansion.leftVector index) (firstExpansion.rightVector index)
      | Sum.inr index => -(secondExpansion.coefficient index *
          inner Real (secondExpansion.leftVector index) (secondExpansion.rightVector index)))
    firstExpansion.trace_summable secondExpansion.trace_summable.neg
  have hDesired : (∑' index : firstExpansion.Index ⊕ secondExpansion.Index,
      match index with
      | Sum.inl index => firstExpansion.coefficient index *
          inner Real (firstExpansion.leftVector index) (firstExpansion.rightVector index)
      | Sum.inr index => (-secondExpansion.coefficient index) *
          inner Real (secondExpansion.leftVector index) (secondExpansion.rightVector index)) =
        (∑' index, firstExpansion.coefficient index *
          inner Real (firstExpansion.leftVector index) (firstExpansion.rightVector index)) -
        ∑' index, secondExpansion.coefficient index *
          inner Real (secondExpansion.leftVector index)
            (secondExpansion.rightVector index) := by
    calc
      _ = ∑' index : firstExpansion.Index ⊕ secondExpansion.Index,
          match index with
          | Sum.inl index => firstExpansion.coefficient index *
              inner Real (firstExpansion.leftVector index)
                (firstExpansion.rightVector index)
          | Sum.inr index => -(secondExpansion.coefficient index *
              inner Real (secondExpansion.leftVector index)
                (secondExpansion.rightVector index)) := by
        apply tsum_congr
        intro index
        cases index <;> simp
      _ = (∑' index, firstExpansion.coefficient index *
            inner Real (firstExpansion.leftVector index)
              (firstExpansion.rightVector index)) +
          ∑' index, -(secondExpansion.coefficient index *
            inner Real (secondExpansion.leftVector index)
              (secondExpansion.rightVector index)) := hTsum
      _ = _ := by rw [tsum_neg, sub_eq_add_neg]
  convert hDesired using 1
  apply tsum_congr
  intro index
  cases index <;> rfl

end
end SummableRankOneOperatorExpansion
end P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
namespace P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Intrinsic nuclear trace is additive under subtraction. -/
theorem intrinsicNuclearTrace_sub
    {first second : E →L[Real] E}
    (firstTrace : IntrinsicNuclearTraceData.{u, v} first)
    (secondTrace : IntrinsicNuclearTraceData.{u, v} second)
    (differenceTrace : IntrinsicNuclearTraceData.{u, v} (first - second)) :
    intrinsicNuclearTrace differenceTrace =
      intrinsicNuclearTrace firstTrace - intrinsicNuclearTrace secondTrace := by
  calc
    intrinsicNuclearTrace differenceTrace =
        (firstTrace.expansion.sub secondTrace.expansion).expansionTrace :=
      (differenceTrace.expansionTrace_eq
        (firstTrace.expansion.sub secondTrace.expansion)).symm
    _ = firstTrace.expansion.expansionTrace -
        secondTrace.expansion.expansionTrace :=
      firstTrace.expansion.sub_expansionTrace secondTrace.expansion
    _ = intrinsicNuclearTrace firstTrace -
        intrinsicNuclearTrace secondTrace := rfl

/-- Public nuclear-subtraction checkpoint. -/
theorem intrinsic_nuclear_trace_subtraction_gate
    {first second : E →L[Real] E}
    (firstTrace : IntrinsicNuclearTraceData.{u, v} first)
    (secondTrace : IntrinsicNuclearTraceData.{u, v} second)
    (differenceTrace : IntrinsicNuclearTraceData.{u, v} (first - second)) :
    intrinsicNuclearTrace differenceTrace =
      intrinsicNuclearTrace firstTrace - intrinsicNuclearTrace secondTrace :=
  intrinsicNuclearTrace_sub firstTrace secondTrace differenceTrace

end
end P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
end JanusFormal

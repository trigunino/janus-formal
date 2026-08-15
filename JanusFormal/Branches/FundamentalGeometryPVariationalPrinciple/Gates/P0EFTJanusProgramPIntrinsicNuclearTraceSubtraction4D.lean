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

/-- Disjoint-sum presentation of the difference of two nuclear operators. -/
def SummableRankOneOperatorExpansion.sub
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
    rw [summable_sum_type]
    constructor
    · simpa using firstExpansion.summable_nuclearNorm
    · simpa using secondExpansion.summable_nuclearNorm
  trace_summable := by
    rw [summable_sum_type]
    constructor
    · simpa using firstExpansion.trace_summable
    · simpa using secondExpansion.trace_summable.neg
  operator_eq_tsum := by
    rw [tsum_sum_type]
    have hFirst := firstExpansion.operator_eq_tsum
    have hSecond := secondExpansion.operator_eq_tsum
    rw [← hFirst, ← hSecond]
    ext vector
    simp [rankOneOperator, sub_eq_add_neg]

@[simp]
theorem SummableRankOneOperatorExpansion.sub_expansionTrace
    {first second : E →L[Real] E}
    (firstExpansion : SummableRankOneOperatorExpansion first)
    (secondExpansion : SummableRankOneOperatorExpansion second) :
    (firstExpansion.sub secondExpansion).expansionTrace =
      firstExpansion.expansionTrace - secondExpansion.expansionTrace := by
  unfold SummableRankOneOperatorExpansion.expansionTrace
  rw [tsum_sum_type]
  simp [sub_eq_add_neg]

/-- Intrinsic nuclear trace is additive under subtraction. -/
theorem intrinsicNuclearTrace_sub
    {first second : E →L[Real] E}
    (firstTrace : IntrinsicNuclearTraceData first)
    (secondTrace : IntrinsicNuclearTraceData second)
    (differenceTrace : IntrinsicNuclearTraceData (first - second)) :
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
    (firstTrace : IntrinsicNuclearTraceData first)
    (secondTrace : IntrinsicNuclearTraceData second)
    (differenceTrace : IntrinsicNuclearTraceData (first - second)) :
    intrinsicNuclearTrace differenceTrace =
      intrinsicNuclearTrace firstTrace - intrinsicNuclearTrace secondTrace :=
  intrinsicNuclearTrace_sub firstTrace secondTrace differenceTrace

end
end P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
end JanusFormal

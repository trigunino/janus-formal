import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Cyclicity of the intrinsic nuclear trace

For a nuclear operator `T` and a bounded operator `B`, the two compositions

```text
B T,
T B
```

have the same trace.  At the rank-one level this is the adjoint identity

```text
⟪B x, y⟫ = ⟪x, B† y⟫.
```

The packet below records one common rank-one presentation of the two
compositions.  It does not accept equality of the scalar traces as an input:
that equality is derived term by term from the Hilbert adjoint and then made
presentation-independent by `IntrinsicNuclearTraceData`.

Keeping the composition expansions explicit is useful for Duhamel formulas,
where the two sides usually arise from different semigroup factorizations and
are propositionally, rather than definitionally, the same nuclear operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceCyclicity4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- One aligned nuclear presentation of `B T` and `T B`.

The left composition sends a rank-one term `(x,y)` to `(B x,y)`.  The right
composition sends it to `(x,B† y)`.  Nuclear-norm and trace summability are
stored separately because this interface is also consumed by concrete heat
kernel estimates. -/
structure CyclicNuclearCompositionExpansionData
    (nuclear bounded : E →L[Real] E) where
  Index : Type u
  coefficient : Index → Real
  leftVector : Index → E
  rightVector : Index → E
  left_nuclearNorm_summable : Summable (fun index =>
    |coefficient index| * ‖bounded (leftVector index)‖ *
      ‖rightVector index‖)
  right_nuclearNorm_summable : Summable (fun index =>
    |coefficient index| * ‖leftVector index‖ *
      ‖ContinuousLinearMap.adjoint bounded (rightVector index)‖)
  left_trace_summable : Summable (fun index =>
    coefficient index *
      inner Real (bounded (leftVector index)) (rightVector index))
  right_trace_summable : Summable (fun index =>
    coefficient index *
      inner Real (leftVector index)
        (ContinuousLinearMap.adjoint bounded (rightVector index)))
  left_operator_eq_tsum : bounded.comp nuclear = ∑' index,
    coefficient index •
      InnerProductSpace.rankOne Real
        (bounded (leftVector index)) (rightVector index)
  right_operator_eq_tsum : nuclear.comp bounded = ∑' index,
    coefficient index •
      InnerProductSpace.rankOne Real
        (leftVector index)
        (ContinuousLinearMap.adjoint bounded (rightVector index))

namespace CyclicNuclearCompositionExpansionData

/-- The aligned presentation of `B T`. -/
def leftExpansion
    {nuclear bounded : E →L[Real] E}
    (data : CyclicNuclearCompositionExpansionData nuclear bounded) :
    SummableRankOneOperatorExpansion (bounded.comp nuclear) where
  Index := data.Index
  coefficient := data.coefficient
  leftVector := fun index => bounded (data.leftVector index)
  rightVector := data.rightVector
  summable_nuclearNorm := data.left_nuclearNorm_summable
  trace_summable := data.left_trace_summable
  operator_eq_tsum := data.left_operator_eq_tsum

/-- The aligned presentation of `T B`. -/
def rightExpansion
    {nuclear bounded : E →L[Real] E}
    (data : CyclicNuclearCompositionExpansionData nuclear bounded) :
    SummableRankOneOperatorExpansion (nuclear.comp bounded) where
  Index := data.Index
  coefficient := data.coefficient
  leftVector := data.leftVector
  rightVector := fun index =>
    ContinuousLinearMap.adjoint bounded (data.rightVector index)
  summable_nuclearNorm := data.right_nuclearNorm_summable
  trace_summable := data.right_trace_summable
  operator_eq_tsum := data.right_operator_eq_tsum

/-- Every aligned pair of rank-one components has the same scalar trace. -/
theorem composition_trace_term_eq
    {nuclear bounded : E →L[Real] E}
    (data : CyclicNuclearCompositionExpansionData nuclear bounded)
    (index : data.Index) :
    data.coefficient index *
        inner Real (bounded (data.leftVector index))
          (data.rightVector index) =
      data.coefficient index *
        inner Real (data.leftVector index)
          (ContinuousLinearMap.adjoint bounded (data.rightVector index)) := by
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- The two certified rank-one presentations have the same trace series. -/
theorem leftExpansionTrace_eq_rightExpansionTrace
    {nuclear bounded : E →L[Real] E}
    (data : CyclicNuclearCompositionExpansionData nuclear bounded) :
    data.leftExpansion.expansionTrace =
      data.rightExpansion.expansionTrace := by
  unfold SummableRankOneOperatorExpansion.expansionTrace
  apply tsum_congr
  intro index
  exact data.composition_trace_term_eq index

/-- Presentation-independent cyclicity of the intrinsic nuclear trace. -/
theorem intrinsicNuclearTrace_comp_comm
    {nuclear bounded : E →L[Real] E}
    (data : CyclicNuclearCompositionExpansionData nuclear bounded)
    (leftTrace : IntrinsicNuclearTraceData (bounded.comp nuclear))
    (rightTrace : IntrinsicNuclearTraceData (nuclear.comp bounded)) :
    intrinsicNuclearTrace leftTrace = intrinsicNuclearTrace rightTrace := by
  calc
    intrinsicNuclearTrace leftTrace =
        data.leftExpansion.expansionTrace :=
      (leftTrace.expansionTrace_eq data.leftExpansion).symm
    _ = data.rightExpansion.expansionTrace :=
      data.leftExpansionTrace_eq_rightExpansionTrace
    _ = intrinsicNuclearTrace rightTrace :=
      rightTrace.expansionTrace_eq data.rightExpansion

/-- Public intrinsic cyclicity checkpoint. -/
theorem intrinsic_nuclear_trace_cyclicity_gate
    (nuclear bounded : E →L[Real] E)
    (data : CyclicNuclearCompositionExpansionData nuclear bounded)
    (leftTrace : IntrinsicNuclearTraceData (bounded.comp nuclear))
    (rightTrace : IntrinsicNuclearTraceData (nuclear.comp bounded)) :
    intrinsicNuclearTrace leftTrace = intrinsicNuclearTrace rightTrace :=
  data.intrinsicNuclearTrace_comp_comm leftTrace rightTrace

end CyclicNuclearCompositionExpansionData

end
end P0EFTJanusProgramPIntrinsicNuclearTraceCyclicity4D
end JanusFormal

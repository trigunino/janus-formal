import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Scalar linearity of the intrinsic nuclear trace

Scaling every coefficient in a summable rank-one presentation by a real scalar
produces a presentation of the scaled operator.  Nuclear summability and trace
summability are preserved, and the scalar expansion trace is multiplied by the
same scalar.

Presentation independence therefore gives

```text
Tr(c • T) = c * Tr(T).
```

This is required to take the intrinsic trace of the scalar factor `-t` in the
Duhamel heat derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceSmul4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Scale one summable rank-one presentation. -/
def SummableRankOneOperatorExpansion.smul
    {operator : E →L[Real] E}
    (data : SummableRankOneOperatorExpansion operator)
    (scalar : Real) :
    SummableRankOneOperatorExpansion (scalar • operator) where
  Index := data.Index
  coefficient := fun index => scalar * data.coefficient index
  leftVector := data.leftVector
  rightVector := data.rightVector
  summable_nuclearNorm := by
    simpa [abs_mul, mul_assoc] using
      data.summable_nuclearNorm.mul_left |scalar|
  trace_summable := by
    simpa [mul_assoc] using data.trace_summable.mul_left scalar
  operator_eq_tsum := by
    rw [data.operator_eq_tsum]
    ext vector
    simp [rankOneOperator, Finset.smul_sum, tsum_mul_left]

@[simp]
theorem SummableRankOneOperatorExpansion.smul_expansionTrace
    {operator : E →L[Real] E}
    (data : SummableRankOneOperatorExpansion operator)
    (scalar : Real) :
    (data.smul scalar).expansionTrace =
      scalar * data.expansionTrace := by
  unfold SummableRankOneOperatorExpansion.expansionTrace
  simp [SummableRankOneOperatorExpansion.smul, tsum_mul_left]

/-- Intrinsic nuclear trace is real-linear under scalar multiplication. -/
theorem intrinsicNuclearTrace_smul
    {operator : E →L[Real] E}
    (scalar : Real)
    (source : IntrinsicNuclearTraceData operator)
    (target : IntrinsicNuclearTraceData (scalar • operator)) :
    intrinsicNuclearTrace target =
      scalar * intrinsicNuclearTrace source := by
  calc
    intrinsicNuclearTrace target =
        (source.expansion.smul scalar).expansionTrace :=
      (target.expansionTrace_eq (source.expansion.smul scalar)).symm
    _ = scalar * source.expansion.expansionTrace :=
      source.expansion.smul_expansionTrace scalar
    _ = scalar * intrinsicNuclearTrace source := rfl

/-- Public scalar-linearity checkpoint. -/
theorem intrinsic_nuclear_trace_smul_gate
    {operator : E →L[Real] E}
    (scalar : Real)
    (source : IntrinsicNuclearTraceData operator)
    (target : IntrinsicNuclearTraceData (scalar • operator)) :
    intrinsicNuclearTrace target =
      scalar * intrinsicNuclearTrace source :=
  intrinsicNuclearTrace_smul scalar source target

end
end P0EFTJanusProgramPIntrinsicNuclearTraceSmul4D
end JanusFormal

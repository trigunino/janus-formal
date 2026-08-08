import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

/-!
# Presentation-independent nuclear trace

A norm-summable rank-one expansion gives a convergent scalar trace series, but
that scalar is not yet intrinsic until independence from the chosen expansion
is proved.  This file isolates that single uniqueness theorem and turns it into
one canonical trace value.

No trace-class API or additional operator is postulated.  The represented
operator, its rank-one expansions and the scalar series are exactly those of
the preceding constructive nuclear packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTrace4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- An intrinsic nuclear trace is one certified rank-one presentation together
with the theorem that every other certified presentation has the same scalar
trace. -/
structure IntrinsicNuclearTraceData
    (operator : E →L[Real] E) where
  expansion : SummableRankOneOperatorExpansion operator
  presentation_independent :
    ∀ other : SummableRankOneOperatorExpansion operator,
      other.expansionTrace = expansion.expansionTrace

/-- Canonical scalar trace of the represented operator. -/
def intrinsicNuclearTrace
    {operator : E →L[Real] E}
    (data : IntrinsicNuclearTraceData operator) : Real :=
  data.expansion.expansionTrace

/-- Every certified rank-one presentation computes the intrinsic trace. -/
theorem IntrinsicNuclearTraceData.expansionTrace_eq
    {operator : E →L[Real] E}
    (data : IntrinsicNuclearTraceData operator)
    (other : SummableRankOneOperatorExpansion operator) :
    other.expansionTrace = intrinsicNuclearTrace data :=
  data.presentation_independent other

/-- The stored presentation computes the canonical trace definitionally. -/
@[simp]
theorem IntrinsicNuclearTraceData.stored_expansionTrace
    {operator : E →L[Real] E}
    (data : IntrinsicNuclearTraceData operator) :
    data.expansion.expansionTrace = intrinsicNuclearTrace data :=
  rfl

/-- Two intrinsic trace certificates for one operator necessarily define the
same scalar. -/
theorem intrinsicNuclearTrace_unique
    {operator : E →L[Real] E}
    (first second : IntrinsicNuclearTraceData operator) :
    intrinsicNuclearTrace first = intrinsicNuclearTrace second := by
  exact (second.presentation_independent first.expansion).symm

/-- Constructor spelling the exact remaining uniqueness obligation. -/
def intrinsicNuclearTraceData_of_expansion
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator)
    (hUnique : ∀ other : SummableRankOneOperatorExpansion operator,
      other.expansionTrace = expansion.expansionTrace) :
    IntrinsicNuclearTraceData operator where
  expansion := expansion
  presentation_independent := hUnique

/-- Existence of intrinsic trace data implies compactness of the represented
operator. -/
theorem IntrinsicNuclearTraceData.operator_compact
    {operator : E →L[Real] E}
    (data : IntrinsicNuclearTraceData operator) :
    IsCompactOperator operator :=
  data.expansion.operator_compact

/-- Public trace-uniqueness checkpoint. -/
theorem intrinsic_nuclear_trace_gate
    (operator : E →L[Real] E)
    (data : IntrinsicNuclearTraceData operator) :
    IsCompactOperator operator ∧
      ∀ expansion : SummableRankOneOperatorExpansion operator,
        expansion.expansionTrace = intrinsicNuclearTrace data :=
  ⟨data.operator_compact, data.expansionTrace_eq⟩

end
end P0EFTJanusProgramPIntrinsicNuclearTrace4D
end JanusFormal

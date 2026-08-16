import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Intrinsic nuclear trace of the zero operator

The empty rank-one expansion is a canonical summable presentation of the zero
operator.  Therefore any intrinsic nuclear-trace certificate for the zero
operator, regardless of its stored presentation, has scalar trace zero by
presentation independence.

This does not postulate trace uniqueness for new operators.  It only extracts
the forced normalization already contained in `IntrinsicNuclearTraceData 0`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceZero4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- Empty rank-one presentation of the zero operator. -/
def zeroRankOneExpansion :
    SummableRankOneOperatorExpansion (0 : E →L[Real] E) where
  Index := Empty
  coefficient := Empty.elim
  leftVector := Empty.elim
  rightVector := Empty.elim
  summable_nuclearNorm := by simp
  trace_summable := by simp
  operator_eq_tsum := by simp

@[simp]
theorem zeroRankOneExpansion_expansionTrace :
    (zeroRankOneExpansion (E := E)).expansionTrace = 0 := by
  simp [zeroRankOneExpansion,
    SummableRankOneOperatorExpansion.expansionTrace]

/-- Every intrinsic trace certificate for the zero operator has trace zero. -/
theorem intrinsicNuclearTrace_zero
    (data : IntrinsicNuclearTraceData (0 : E →L[Real] E)) :
    intrinsicNuclearTrace data = 0 := by
  have h := data.expansionTrace_eq (zeroRankOneExpansion (E := E))
  simpa using h.symm

/-- Public zero-trace normalization checkpoint. -/
theorem intrinsic_nuclear_trace_zero_gate
    (data : IntrinsicNuclearTraceData (0 : E →L[Real] E)) :
    intrinsicNuclearTrace data = 0 ∧
    (zeroRankOneExpansion (E := E)).expansionTrace = 0 :=
  ⟨intrinsicNuclearTrace_zero data,
    zeroRankOneExpansion_expansionTrace⟩

end
end P0EFTJanusProgramPIntrinsicNuclearTraceZero4D
end JanusFormal

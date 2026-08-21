import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D

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
open P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]

/-- Empty rank-one presentation of the zero operator. -/
def zeroRankOneExpansion :
    SummableRankOneOperatorExpansion.{v, u} (0 : E →L[Real] E) where
  Index := ULift.{v} Empty
  coefficient := fun index => index.down.elim
  leftVector := fun index => index.down.elim
  rightVector := fun index => index.down.elim
  summable_nuclearNorm := by simp
  trace_summable := by simp
  operator_eq_tsum := by simp

@[simp]
theorem zeroRankOneExpansion_expansionTrace :
    (zeroRankOneExpansion (E := E)).expansionTrace = 0 := by
  simp [zeroRankOneExpansion,
    SummableRankOneOperatorExpansion.expansionTrace]

/-- Any existing intrinsic trace certificate on the same Hilbert space
canonically supplies the intrinsic trace certificate for the zero operator. -/
def intrinsicNuclearTraceData_zero_of_source
    [CompleteSpace E]
    {operator : E →L[Real] E}
    (source : IntrinsicNuclearTraceData.{u, v} operator) :
    IntrinsicNuclearTraceData.{u, v} (0 : E →L[Real] E) where
  expansion := zeroRankOneExpansion
  presentation_independent := by
    intro other
    let combinedRaw := source.expansion.sub other
    let combined := transportExpansionOperator combinedRaw (sub_zero operator)
    have h : source.expansion.expansionTrace - other.expansionTrace =
        source.expansion.expansionTrace := by
      calc
        source.expansion.expansionTrace - other.expansionTrace =
            combinedRaw.expansionTrace :=
          (source.expansion.sub_expansionTrace other).symm
        _ = combined.expansionTrace := by
          exact (transportExpansionOperator_expansionTrace combinedRaw
            (sub_zero operator)).symm
        _ = source.expansion.expansionTrace :=
          source.presentation_independent combined
    simpa using (sub_eq_self.mp h)

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

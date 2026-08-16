import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Transport intrinsic nuclear traces across equality of operators

`IntrinsicNuclearTraceData` is dependently typed by the bounded operator whose
trace it certifies.  Exact geometric identifications often produce an equality
of operators rather than definitional equality.

This file transports the complete intrinsic trace certificate through such an
equality.  The selected expansion and its scalar trace are unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicNuclearTrace4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace IntrinsicNuclearTraceData

/-- Reinterpret an intrinsic nuclear trace certificate through operator
equality. -/
def transportOperator
    {first second : E →L[Real] E}
    (data : IntrinsicNuclearTraceData.{u, v} first)
    (hOperator : first = second) :
    IntrinsicNuclearTraceData.{u, v} second := by
  cases hOperator
  exact data

@[simp]
theorem transportOperator_intrinsicNuclearTrace
    {first second : E →L[Real] E}
    (data : IntrinsicNuclearTraceData.{u, v} first)
    (hOperator : first = second) :
    intrinsicNuclearTrace (transportOperator data hOperator) =
      intrinsicNuclearTrace data := by
  cases hOperator
  rfl

end IntrinsicNuclearTraceData

/-- Public intrinsic-trace transport checkpoint. -/
theorem intrinsic_nuclear_trace_transport_gate
    {first second : E →L[Real] E}
    (data : IntrinsicNuclearTraceData.{u, v} first)
    (hOperator : first = second) :
    intrinsicNuclearTrace (IntrinsicNuclearTraceData.transportOperator data hOperator) =
      intrinsicNuclearTrace data :=
  IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace data hOperator

end
end P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
end JanusFormal
